-- Prove2me | solution 1 for DiscreteConvex.NetworkFlowsB.mcfp0_integrality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:41:49.518987+00:00
-- url     : https://prove2.me/submissions/45aecfb2-9a88-4ed3-8230-11ec72ae1c4e

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_LConvexPolyhedronR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetMCFP0
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvexArc

open Classical
open scoped Pointwise

namespace DiscreteConvex.NetworkFlowsB

section DiffSetSec
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A system of (conditional) difference constraints. -/
def DiffSet {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ) : Set (V → ℝ) :=
  {p | ∀ i, Q i → p (u i) - p (v i) ≤ c i}

/-- The integer points. -/
def ZPts : Set (V → ℝ) := {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)}

lemma sum_diff_coef (p : V → ℝ) (u v : V) :
    ∑ w, ((if w = u then (1:ℝ) else 0) - (if w = v then (1:ℝ) else 0)) * p w = p u - p v := by
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

lemma isPolyhedron_of_fintype {W : Type*} [Fintype W] {ι : Type*} [Fintype ι]
    (a : ι → W → ℝ) (b : ι → ℝ) :
    IsPolyhedron {x : W → ℝ | ∀ i, ∑ w, a i w * x w ≤ b i} := by
  refine ⟨Fintype.card ι, fun j => a ((Fintype.equivFin ι).symm j),
    fun j => b ((Fintype.equivFin ι).symm j), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h j; exact h _
  · intro h i
    have := h (Fintype.equivFin ι i)
    simpa using this

lemma diffSet_polyhedron {ι : Type*} [Fintype ι] (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ) :
    IsPolyhedron (DiffSet Q u v c) := by
  have h := isPolyhedron_of_fintype
    (fun i w => if Q i then ((if w = u i then (1:ℝ) else 0) - (if w = v i then (1:ℝ) else 0)) else 0)
    (fun i => if Q i then c i else 0)
  convert h using 1
  ext p
  simp only [DiffSet, Set.mem_setOf_eq]
  apply forall_congr'
  intro i
  by_cases hQ : Q i
  · simp only [hQ, if_true, true_implies, sum_diff_coef]
  · simp [hQ]

lemma diffSet_sup {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ)
    {p q : V → ℝ} (hp : p ∈ DiffSet Q u v c) (hq : q ∈ DiffSet Q u v c) :
    p ⊔ q ∈ DiffSet Q u v c := by
  intro i hi
  have h1 := hp i hi
  have h2 := hq i hi
  simp only [Pi.sup_apply]
  show max _ _ - max _ _ ≤ _
  rcases max_cases (p (u i)) (q (u i)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · linarith [le_max_left (p (v i)) (q (v i))]
  · linarith [le_max_right (p (v i)) (q (v i))]

lemma diffSet_inf {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ)
    {p q : V → ℝ} (hp : p ∈ DiffSet Q u v c) (hq : q ∈ DiffSet Q u v c) :
    p ⊓ q ∈ DiffSet Q u v c := by
  intro i hi
  have h1 := hp i hi
  have h2 := hq i hi
  simp only [Pi.inf_apply]
  show min _ _ - min _ _ ≤ _
  rcases min_cases (p (v i)) (q (v i)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · linarith [min_le_left (p (u i)) (q (u i))]
  · linarith [min_le_right (p (u i)) (q (u i))]

lemma diffSet_trans {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ)
    {p : V → ℝ} (hp : p ∈ DiffSet Q u v c) (α : ℝ) :
    (fun w => p w + α) ∈ DiffSet Q u v c := by
  intro i hi
  have h1 := hp i hi
  simp only
  linarith

lemma diffSet_convex {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ) :
    Convex ℝ (DiffSet Q u v c) := by
  intro p hp q hq a b ha hb hab i hi
  have h1 := hp i hi
  have h2 := hq i hi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : a * p (u i) + b * q (u i) - (a * p (v i) + b * q (v i)) =
      a * (p (u i) - p (v i)) + b * (q (u i) - q (v i)) := by ring
  rw [this]
  calc a * (p (u i) - p (v i)) + b * (q (u i) - q (v i)) ≤ a * c i + b * c i := by
        gcongr
    _ = c i := by rw [← add_mul, hab, one_mul]

lemma floor_diff_le {a b : ℝ} {n : ℤ} (h : a - b ≤ n) : ((⌊a⌋ : ℤ) : ℝ) - ⌊b⌋ ≤ n := by
  have h1 : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
  have h2 : b < ⌊b⌋ + 1 := Int.lt_floor_add_one b
  have h3 : ((⌊a⌋ : ℤ) : ℝ) < ⌊b⌋ + n + 1 := by linarith
  have h4 : ⌊a⌋ < ⌊b⌋ + n + 1 := by exact_mod_cast h3
  have h5 : ⌊a⌋ - ⌊b⌋ ≤ n := by omega
  exact_mod_cast h5

lemma ceil_diff_le {a b : ℝ} {n : ℤ} (h : a - b ≤ n) : ((⌈a⌉ : ℤ) : ℝ) - ⌈b⌉ ≤ n := by
  have h1 : (⌈b⌉ : ℝ) ≥ b := Int.le_ceil b
  have h2 : a > ⌈a⌉ - 1 := Int.ceil_lt_add_one a |> fun h => by linarith
  have h3 : ((⌈a⌉ : ℤ) : ℝ) < ⌈b⌉ + n + 1 := by linarith
  have h4 : ⌈a⌉ < ⌈b⌉ + n + 1 := by exact_mod_cast h3
  have h5 : ⌈a⌉ - ⌈b⌉ ≤ n := by omega
  exact_mod_cast h5

lemma diffSet_floor {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ)
    (hc : ∀ i, ∃ n : ℤ, c i = n) {p : V → ℝ} (hp : p ∈ DiffSet Q u v c) :
    (fun w => ((⌊p w⌋ : ℤ) : ℝ)) ∈ DiffSet Q u v c := by
  intro i hi
  obtain ⟨n, hn⟩ := hc i
  have := hp i hi
  rw [hn] at this ⊢
  exact floor_diff_le this

lemma diffSet_ceil {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ)
    (hc : ∀ i, ∃ n : ℤ, c i = n) {p : V → ℝ} (hp : p ∈ DiffSet Q u v c) :
    (fun w => ((⌈p w⌉ : ℤ) : ℝ)) ∈ DiffSet Q u v c := by
  intro i hi
  obtain ⟨n, hn⟩ := hc i
  have := hp i hi
  rw [hn] at this ⊢
  exact ceil_diff_le this

lemma fract_eq_zero_of_int (t : ℝ) (h : ∃ n : ℤ, t = n) : Int.fract t = 0 := by
  obtain ⟨n, hn⟩ := h; rw [hn]; exact Int.fract_intCast n

lemma int_of_fract_eq_zero (t : ℝ) (h : Int.fract t = 0) : ∃ n : ℤ, t = n := by
  refine ⟨⌊t⌋, ?_⟩
  have := Int.floor_add_fract t
  rw [h, add_zero] at this
  exact this.symm

/-- The core integrality step: a point of a difference-constraint system with integer bounds is
a convex combination of integer points of the system. -/
lemma diffSet_hull {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ)
    (hc : ∀ i, ∃ n : ℤ, c i = n) :
    ∀ n : ℕ, ∀ p ∈ DiffSet Q u v c,
      (Finset.univ.filter (fun w => Int.fract (p w) ≠ 0)).card = n →
      p ∈ convexHull ℝ (DiffSet Q u v c ∩ ZPts) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hp hn
  by_cases hF : (Finset.univ.filter (fun w => Int.fract (p w) ≠ 0)) = ∅
  · -- p is integral
    apply subset_convexHull
    refine ⟨hp, fun w => ?_⟩
    apply int_of_fract_eq_zero
    by_contra h
    have : w ∈ Finset.univ.filter (fun w => Int.fract (p w) ≠ 0) := by simp [h]
    rw [hF] at this; simp at this
  · obtain ⟨w0, hw0F, hw0min⟩ := Finset.exists_min_image
      (Finset.univ.filter (fun w => Int.fract (p w) ≠ 0)) (fun w => Int.fract (p w))
      (Finset.nonempty_iff_ne_empty.2 hF)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw0F hw0min
    set θ := Int.fract (p w0) with hθ
    have hθ0 : 0 < θ := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hw0F)
    have hθ1 : θ < 1 := Int.fract_lt_one _
    -- the integer point q = ⌈p⌉
    set q : V → ℝ := fun w => ((⌈p w⌉ : ℤ) : ℝ) with hq
    have hqS : q ∈ DiffSet Q u v c := diffSet_ceil Q u v c hc hp
    have hqZ : q ∈ ZPts := fun w => ⟨⌈p w⌉, rfl⟩
    -- the residual point
    set p' : V → ℝ := fun w => (p w - θ * q w) / (1 - θ) with hp'
    have h1θ : 0 < 1 - θ := by linarith
    -- key facts on q and p
    have hqp : ∀ w, q w - p w = if Int.fract (p w) = 0 then 0 else 1 - Int.fract (p w) := by
      intro w
      simp only [hq]
      split_ifs with h
      · obtain ⟨k, hk⟩ := int_of_fract_eq_zero _ h
        rw [hk]; simp
      · have hfl := Int.floor_add_fract (p w)
        have hceil : ⌈p w⌉ = ⌊p w⌋ + 1 := by
          rw [Int.ceil_eq_iff]
          constructor
          · push_cast
            have : 0 < Int.fract (p w) := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm h)
            linarith
          · push_cast
            have := Int.fract_lt_one (p w); linarith
        rw [hceil]; push_cast; linarith
    have hqp_nonneg : ∀ w, 0 ≤ q w - p w := by
      intro w; rw [hqp]; split_ifs
      · exact le_rfl
      · linarith [Int.fract_lt_one (p w)]
    have hqp_le : ∀ w, q w - p w ≤ 1 - θ := by
      intro w; rw [hqp]; split_ifs with h
      · linarith
      · have := hw0min w h; linarith
    have hp'S : p' ∈ DiffSet Q u v c := by
      intro i hi
      obtain ⟨m, hm⟩ := hc i
      have h1 := hp i hi
      have h2 := hqS i hi
      simp only [hp']
      rw [div_sub_div_same, div_le_iff₀ h1θ]
      rw [hm] at h1 h2 ⊢
      -- q u - q v is an integer ≤ m, so either = m or ≤ m - 1
      have hint : ((⌈p (u i)⌉ : ℤ) : ℝ) - ⌈p (v i)⌉ ≤ m := h2
      have hint' : ⌈p (u i)⌉ - ⌈p (v i)⌉ ≤ m := by exact_mod_cast hint
      rcases eq_or_lt_of_le hint' with heq | hlt
      · have heq' : q (u i) - q (v i) = m := by
          simp only [hq]; exact_mod_cast heq
        nlinarith
      · have hlt' : q (u i) - q (v i) ≤ m - 1 := by
          simp only [hq]
          have : ⌈p (u i)⌉ - ⌈p (v i)⌉ ≤ m - 1 := by omega
          exact_mod_cast this
        have e1 := hqp_nonneg (u i)
        have e2 := hqp_le (v i)
        nlinarith
    have hp'card : (Finset.univ.filter (fun w => Int.fract (p' w) ≠ 0)).card < n := by
      rw [← hn]
      apply Finset.card_lt_card
      refine ⟨fun w hw => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        intro h0
        apply hw
        have hpq : p w = q w := by
          have := hqp w; rw [if_pos h0] at this; linarith
        simp only [hp', hpq]
        have : (q w - θ * q w) / (1 - θ) = q w := by
          field_simp
        rw [this]; exact fract_eq_zero_of_int _ (hqZ w)
      · have hw0 : w0 ∈ Finset.univ.filter (fun w => Int.fract (p w) ≠ 0) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hw0F
        have := hsub hw0
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        apply this
        have hq0 : q w0 - p w0 = 1 - θ := by rw [hqp, if_neg hw0F]
        have hfl := Int.floor_add_fract (p w0)
        simp only [hp']
        have : (p w0 - θ * q w0) / (1 - θ) = ⌊p w0⌋ := by
          rw [div_eq_iff h1θ.ne']
          nlinarith
        rw [this]; exact fract_eq_zero_of_int _ ⟨_, rfl⟩
    have hp'H := ih _ hp'card p' hp'S rfl
    have hqH : q ∈ convexHull ℝ (DiffSet Q u v c ∩ ZPts) := subset_convexHull ℝ _ ⟨hqS, hqZ⟩
    have hcomb := (convex_convexHull ℝ (DiffSet Q u v c ∩ ZPts)) hqH hp'H hθ0.le h1θ.le
      (by ring)
    convert hcomb using 1
    funext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp']
    field_simp
    ring

lemma diffSet_integral {ι : Type*} [Fintype ι] (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ)
    (hc : ∀ i, ∃ n : ℤ, c i = n) :
    IsIntegralPolyhedron (DiffSet Q u v c) := by
  unfold IsIntegralPolyhedron
  apply le_antisymm
  · intro p hp
    exact diffSet_hull Q u v c hc _ p hp rfl
  · exact convexHull_min Set.inter_subset_left (diffSet_convex Q u v c)

end DiffSetSec

namespace PCFarkas

open Matrix

set_option linter.unusedSectionVars false

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

def PFeas (M : Matrix κ ι ℝ) (r : κ → ℝ) (z : ι → ℝ) : Prop := (∀ j, 0 ≤ z j) ∧ M *ᵥ z = r

noncomputable def supp (z : ι → ℝ) : Finset ι := Finset.univ.filter (fun j => z j ≠ 0)

def ColLI (M : Matrix κ ι ℝ) (S : Finset ι) : Prop :=
  LinearIndependent ℝ (fun j : S => Mᵀ (j : ι))

lemma mem_supp {z : ι → ℝ} {j : ι} : j ∈ supp z ↔ z j ≠ 0 := by simp [supp]

lemma sum_sub_eq_mulVec (M : Matrix κ ι ℝ) (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ j, j ∉ S → w j = 0) :
    ∑ j : S, w j • Mᵀ (j : ι) = M *ᵥ w := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul, mulVec, dotProduct]
  rw [Finset.sum_coe_sort S (fun j => w j * M i j)]
  rw [Finset.sum_subset (Finset.subset_univ S)]
  · exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · intro j _ hj; simp [hw j hj]

lemma reduce (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (L : ℝ)
    (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z) :
    ∀ n, ∀ z, (supp z).card = n → PFeas M r z →
      ∃ z', PFeas M r z' ∧ c ⬝ᵥ z' ≤ c ⬝ᵥ z ∧ supp z' ⊆ supp z ∧ ColLI M (supp z') := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hn hz
  by_cases hli : ColLI M (supp z)
  · exact ⟨z, hz, le_rfl, subset_rfl, hli⟩
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
  let d : ι → ℝ := fun j => if h : j ∈ supp z then g ⟨j, h⟩ else 0
  have hdS : ∀ j, j ∉ supp z → d j = 0 := by intro j hj; simp [d, hj]
  have hMd : M *ᵥ d = 0 := by
    rw [← sum_sub_eq_mulVec M (supp z) d hdS]
    convert hg using 2 with j
    simp [d]
  have hdi0 : d i0 ≠ 0 := by simpa [d] using hi0
  have hzpos : ∀ j, 0 ≤ z j := hz.1
  -- unboundedness contradiction
  have unb : ∀ e : ι → ℝ, M *ᵥ e = 0 → (∀ j, 0 ≤ e j) → c ⬝ᵥ e < 0 → False := by
    intro e hMe he hce
    set s := (c ⬝ᵥ z - L + 1) / (-(c ⬝ᵥ e)) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith [hL z hz]) (by linarith)
    have hf : PFeas M r (z + s • e) := ⟨fun j => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (hzpos j) (mul_nonneg hs0 (he j)), by
      rw [mulVec_add, mulVec_smul, hMe, smul_zero, add_zero, hz.2]⟩
    have := hL _ hf
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have hse : s * (c ⬝ᵥ e) = -(c ⬝ᵥ z - L + 1) := by
      have hne : -(c ⬝ᵥ e) ≠ 0 := by linarith
      have h2 : (c ⬝ᵥ z - L + 1) / -(c ⬝ᵥ e) * -(c ⬝ᵥ e) = c ⬝ᵥ z - L + 1 := div_mul_cancel₀ _ hne
      rw [hs]; linear_combination -h2
    linarith
  obtain ⟨e, hMe, heS, hce, j0, hj0⟩ : ∃ e : ι → ℝ, M *ᵥ e = 0 ∧ (∀ j, j ∉ supp z → e j = 0) ∧
      c ⬝ᵥ e ≤ 0 ∧ ∃ j, e j < 0 := by
    obtain ⟨d1, hMd1, hd1S, hcd1, hd1i0⟩ : ∃ d1 : ι → ℝ, M *ᵥ d1 = 0 ∧
        (∀ j, j ∉ supp z → d1 j = 0) ∧ c ⬝ᵥ d1 ≤ 0 ∧ d1 i0 ≠ 0 := by
      by_cases h : c ⬝ᵥ d ≤ 0
      · exact ⟨d, hMd, hdS, h, hdi0⟩
      · refine ⟨-d, by rw [mulVec_neg, hMd, neg_zero], fun j hj => by simp [hdS j hj], ?_, ?_⟩
        · rw [dotProduct_neg]; linarith
        · simpa using hdi0
    by_cases hneg : ∃ j, d1 j < 0
    · exact ⟨d1, hMd1, hd1S, hcd1, hneg⟩
    push_neg at hneg
    rcases hcd1.lt_or_eq with hlt | heq
    · exact (unb d1 hMd1 hneg hlt).elim
    · refine ⟨-d1, by rw [mulVec_neg, hMd1, neg_zero], fun j hj => by simp [hd1S j hj],
        by rw [dotProduct_neg, heq, neg_zero], i0, ?_⟩
      have := lt_of_le_of_ne (hneg i0) (Ne.symm hd1i0)
      simp only [Pi.neg_apply]; linarith
  let P := Finset.univ.filter (fun j => e j < 0)
  obtain ⟨jm, hjmP, hjm⟩ := P.exists_min_image (fun j => z j / (-e j)) ⟨j0, by simp [P, hj0]⟩
  have hejm : e jm < 0 := by simpa [P] using hjmP
  set t := z jm / (-e jm) with ht
  have ht0 : 0 ≤ t := div_nonneg (hzpos jm) (by linarith)
  let z' := z + t • e
  have hz' : PFeas M r z' := by
    refine ⟨fun j => ?_, by simp only [z']; rw [mulVec_add, mulVec_smul, hMe, smul_zero, add_zero, hz.2]⟩
    simp only [z', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hej : e j < 0
    · have h1 : t ≤ z j / (-e j) := hjm j (by simp [P, hej])
      rw [le_div_iff₀ (by linarith)] at h1
      linarith
    · push_neg at hej
      exact add_nonneg (hzpos j) (mul_nonneg ht0 hej)
  have hsub : supp z' ⊆ supp z := by
    intro j hj
    rw [mem_supp] at hj ⊢
    intro hzj
    apply hj
    have : e j = 0 := by
      by_contra hne
      exact absurd (heS j) (by
        intro h'
        have : j ∉ supp z := by rw [mem_supp]; exact fun h => h hzj
        exact hne (h' this))
    simp [z', hzj, this]
  have hjm_in : jm ∈ supp z := by
    by_contra h; exact absurd (heS jm h) (ne_of_lt hejm)
  have hjm_out : jm ∉ supp z' := by
    rw [mem_supp, not_not]
    simp only [z', Pi.add_apply, Pi.smul_apply, smul_eq_mul, ht]
    have hne : e jm ≠ 0 := ne_of_lt hejm
    rw [div_neg, neg_mul, div_mul_cancel₀ _ hne]; ring
  have hlt : (supp z').card < n := by
    rw [← hn]
    exact Finset.card_lt_card ⟨hsub, fun h => hjm_out (h hjm_in)⟩
  obtain ⟨z'', h1, h2, h3, h4⟩ := ih _ hlt z' rfl hz'
  refine ⟨z'', h1, le_trans h2 ?_, h3.trans hsub, h4⟩
  simp only [z', dotProduct_add, dotProduct_smul, smul_eq_mul]
  nlinarith

lemma colLI_unique (M : Matrix κ ι ℝ) (z1 z2 : ι → ℝ) (h : supp z1 = supp z2)
    (hli : ColLI M (supp z1)) (hM : M *ᵥ z1 = M *ᵥ z2) : z1 = z2 := by
  have hw : ∀ j, j ∉ supp z1 → (z1 - z2) j = 0 := by
    intro j hj
    have hj2 : j ∉ supp z2 := h ▸ hj
    rw [mem_supp, not_not] at hj hj2
    simp [hj, hj2]
  have hsum := sum_sub_eq_mulVec M (supp z1) (z1 - z2) hw
  rw [mulVec_sub, hM, sub_self] at hsum
  have := Fintype.linearIndependent_iff.mp hli (fun j => (z1 - z2) j) hsum
  funext j
  by_cases hj : j ∈ supp z1
  · have := this ⟨j, hj⟩; simp only [Pi.sub_apply] at this; linarith
  · have := hw j hj; simp only [Pi.sub_apply] at this; linarith

lemma attain (M : Matrix κ ι ℝ) (r : κ → ℝ) (c : ι → ℝ) (L : ℝ)
    (hL : ∀ z, PFeas M r z → L ≤ c ⬝ᵥ z) (z0 : ι → ℝ) (hz0 : PFeas M r z0) :
    ∃ zs, PFeas M r zs ∧ ColLI M (supp zs) ∧ ∀ z, PFeas M r z → c ⬝ᵥ zs ≤ c ⬝ᵥ z := by
  let F : Set (ι → ℝ) := {z | PFeas M r z ∧ ColLI M (supp z)}
  have hinj : Set.InjOn supp F := by
    intro z1 h1 z2 h2 h
    exact colLI_unique M z1 z2 h h1.2 (by rw [h1.1.2, h2.1.2])
  have hfin : F.Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  obtain ⟨z1, hz1, _, _, hz1li⟩ := reduce M r c L hL _ z0 rfl hz0
  obtain ⟨zs, hzs, hmin⟩ := Set.exists_min_image F (fun z => c ⬝ᵥ z) hfin ⟨z1, hz1, hz1li⟩
  refine ⟨zs, hzs.1, hzs.2, fun z hz => ?_⟩
  obtain ⟨z', hz', hc', _, hli'⟩ := reduce M r c L hL _ z rfl hz
  exact le_trans (hmin z' ⟨hz', hli'⟩) hc'


def cone (M : Matrix κ ι ℝ) : Set (κ → ℝ) := (M.mulVecLin) '' {z | ∀ j, 0 ≤ z j}

lemma cone_closed (M : Matrix κ ι ℝ) : IsClosed (cone M) := by
  have heq : cone M = ⋃ (S : Finset ι) (_ : ColLI M S),
      (Fintype.linearCombination ℝ (fun j : S => Mᵀ (j : ι))) '' {w | ∀ j, 0 ≤ w j} := by
    ext t
    simp only [cone, Set.mem_image, Set.mem_setOf_eq, Set.mem_iUnion, mulVecLin_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨z', hz', _, _, hli⟩ := reduce M (M *ᵥ z) 0 0 (fun _ _ => by simp) _ z rfl ⟨hz, rfl⟩
      refine ⟨supp z', hli, fun j => z' j, fun j => hz'.1 j, ?_⟩
      rw [Fintype.linearCombination_apply, sum_sub_eq_mulVec M (supp z') z'
        (fun j hj => by rw [mem_supp, not_not] at hj; exact hj), hz'.2]
    · rintro ⟨S, _, w, hw, rfl⟩
      refine ⟨fun j => if h : j ∈ S then w ⟨j, h⟩ else 0, fun j => ?_, ?_⟩
      · by_cases h : j ∈ S <;> simp [h, hw]
      · rw [Fintype.linearCombination_apply, ← sum_sub_eq_mulVec M S _ (fun j hj => by simp [hj])]
        simp
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro S
  apply isClosed_iUnion_of_finite
  intro hli
  have hinj := linearIndependent_iff_injective_fintypeLinearCombination.mp hli
  have hker : LinearMap.ker (Fintype.linearCombination ℝ (fun j : S => Mᵀ (j : ι))) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  apply (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap
  have : {w : S → ℝ | ∀ j, 0 ≤ w j} = ⋂ j, {w | 0 ≤ w j} := by ext; simp
  rw [this]
  exact isClosed_iInter (fun j => isClosed_le continuous_const (continuous_apply j))

lemma farkas (M : Matrix κ ι ℝ) (t : κ → ℝ) (ht : t ∉ cone M) :
    ∃ y : κ → ℝ, (∀ j, 0 ≤ (y ᵥ* M) j) ∧ y ⬝ᵥ t < 0 := by
  have hconv : Convex ℝ (cone M) := by
    apply Convex.linear_image
    have : {z : ι → ℝ | ∀ j, 0 ≤ z j} = Set.Ici 0 := by ext; simp [Pi.le_def]
    rw [this]; exact convex_Ici 0
  obtain ⟨f, u, hfu, hut⟩ := geometric_hahn_banach_closed_point hconv (cone_closed M) ht
  have h0 : 0 < u := by
    have := hfu 0 ⟨0, fun _ => le_rfl, by simp⟩
    simpa using this
  have hneg : ∀ a ∈ cone M, f a ≤ 0 := by
    intro a ha
    by_contra h
    push_neg at h
    obtain ⟨z, hz, rfl⟩ := ha
    have hs : 0 ≤ u / f (M.mulVecLin z) + 1 := by positivity
    have hmem : (u / f (M.mulVecLin z) + 1) • M.mulVecLin z ∈ cone M :=
      ⟨(u / f (M.mulVecLin z) + 1) • z, fun j => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hs (hz j), by simp⟩
    have := hfu _ hmem
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ (ne_of_gt h)] at this
    linarith
  have hf : ∀ v : κ → ℝ, f v = ∑ i, v i * f (fun j => if i = j then 1 else 0) := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap v
    simpa using this
  refine ⟨fun i => - f (fun j => if i = j then 1 else 0), fun j => ?_, ?_⟩
  · have hmem : Mᵀ j ∈ cone M := ⟨Pi.single j 1, fun k => by
      by_cases h : k = j
      · subst h; simp
      · simp [h], by ext i; simp [mulVec, dotProduct, Pi.single_apply]⟩
    have := hneg _ hmem
    rw [hf] at this
    simp only [vecMul, dotProduct, transpose_apply] at this ⊢
    have : ∑ x, -f (fun j => if x = j then 1 else 0) * M x j =
        -∑ x, M x j * f (fun j => if x = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith
  · have := hf t
    simp only [dotProduct]
    have : ∑ x, -f (fun j => if x = j then 1 else 0) * t x =
        -∑ x, t x * f (fun j => if x = j then 1 else 0) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith

end PCFarkas

section PC
set_option linter.unusedSectionVars false

lemma farkasL {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (L : κ → (ι → ℝ) →ₗ[ℝ] ℝ) (c : (ι → ℝ) →ₗ[ℝ] ℝ)
    (h : ∀ d, (∀ k, L k d ≤ 0) → 0 ≤ c d) :
    ∃ lam : κ → ℝ, (∀ k, 0 ≤ lam k) ∧ ∀ z, c z = - ∑ k, lam k * L k z := by
  have hlin : ∀ (g : (ι → ℝ) →ₗ[ℝ] ℝ) (z : ι → ℝ),
      g z = ∑ i, z i * g (fun j => if i = j then 1 else 0) := by
    intro g z
    have := LinearMap.pi_apply_eq_sum_univ g z
    simpa using this
  let M : Matrix ι κ ℝ := fun i k => - L k (fun j => if i = j then 1 else 0)
  let t : ι → ℝ := fun i => c (fun j => if i = j then 1 else 0)
  by_cases ht : t ∈ PCFarkas.cone M
  · obtain ⟨w, hw, hMw⟩ := ht
    refine ⟨w, hw, fun z => ?_⟩
    have hti : ∀ i, t i = ∑ k, M i k * w k := fun i => by
      rw [← hMw]; simp [Matrix.mulVec, dotProduct]
    rw [hlin c z]
    simp_rw [hlin (L _) z]
    calc ∑ i, z i * c (fun j => if i = j then 1 else 0) = ∑ i, z i * t i := rfl
      _ = ∑ i, z i * ∑ k, M i k * w k := by simp_rw [hti]
      _ = _ := by
        simp only [M, Finset.mul_sum]
        rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
  · exfalso
    obtain ⟨y, hy, hyt⟩ := PCFarkas.farkas M t ht
    have h1 : ∀ k, L k y ≤ 0 := by
      intro k
      have := hy k
      simp only [Matrix.vecMul, dotProduct, M] at this
      rw [hlin (L k) y]
      have e : ∑ x, y x * -(L k) (fun j => if x = j then 1 else 0) =
          -∑ x, y x * (L k) (fun j => if x = j then 1 else 0) := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      linarith
    have h2 : c y < 0 := by
      rw [hlin c y]; simpa [dotProduct, t] using hyt
    linarith [h y h1]

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma bnd_pair (tail head : A → V) (q : V → ℝ) (xi : A → ℝ) :
    ∑ v, q v * Boundary tail head xi v = ∑ a, xi a * Coboundary tail head q a := by
  have h1 : ∀ g : A → V, ∑ v, q v * ∑ a, (if g a = v then xi a else 0) = ∑ a, xi a * q (g a) := by
    intro g
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp only [Boundary, Coboundary, Finset.sum_filter, mul_sub, Finset.sum_sub_distrib, h1]

abbrev Iota (V A : Type*) := A ⊕ A ⊕ Option V

def mkv (xi s : A → ℝ) (y : V → ℝ) (r : ℝ) : Iota V A → ℝ
  | .inl a => xi a
  | .inr (.inl a) => s a
  | .inr (.inr (some v)) => y v
  | .inr (.inr none) => r

def PP (i : Iota V A) : (Iota V A → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i

@[simp] lemma PP_apply (i : Iota V A) (z : Iota V A → ℝ) : PP i z = z i := rfl

def Lbd (tail head : A → V) (v : V) : (Iota V A → ℝ) →ₗ[ℝ] ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => tail a = v), PP (.inl a) -
    ∑ a ∈ Finset.univ.filter (fun a => head a = v), PP (.inl a)

lemma Lbd_apply (tail head : A → V) (v : V) (z : Iota V A → ℝ) :
    Lbd tail head v z = Boundary tail head (fun a => z (.inl a)) v := by
  simp [Lbd, Boundary, LinearMap.sub_apply, LinearMap.sum_apply]

abbrev Kap (V A : Type*) (m : ℕ) (ma : A → ℕ) := (Σ a, Fin (ma a)) ⊕ Fin m ⊕ V ⊕ V

def Lall (tail head : A → V) (m : ℕ) (C : Fin m → Option V → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) : Kap V A m ma → (Iota V A → ℝ) →ₗ[ℝ] ℝ
  | .inl ⟨a, j⟩ => Ca a j false • PP (.inl a) + Ca a j true • PP (.inr (.inl a))
  | .inr (.inl i) => C i none • PP (.inr (.inr none)) + ∑ v, C i (some v) • PP (.inr (.inr (some v)))
  | .inr (.inr (.inl v)) => PP (.inr (.inr (some v))) - Lbd tail head v
  | .inr (.inr (.inr v)) => Lbd tail head v - PP (.inr (.inr (some v)))

def ball (m : ℕ) (B : Fin m → ℝ) (ma : A → ℕ) (Ba : ∀ a, Fin (ma a) → ℝ) :
    Kap V A m ma → ℝ
  | .inl ⟨a, j⟩ => Ba a j
  | .inr (.inl i) => B i
  | .inr (.inr _) => 0

def cobj : (Iota V A → ℝ) →ₗ[ℝ] ℝ := ∑ a, PP (.inr (.inl a)) + PP (.inr (.inr none))

lemma cobj_apply (z : Iota V A → ℝ) :
    (cobj : (Iota V A → ℝ) →ₗ[ℝ] ℝ) z = ∑ a, z (.inr (.inl a)) + z (.inr (.inr none)) := by
  simp [cobj, LinearMap.sum_apply]

lemma Lall_arc (tail head : A → V) (m : ℕ) (C : Fin m → Option V → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) (a : A) (j : Fin (ma a)) (z : Iota V A → ℝ) :
    Lall tail head m C ma Ca (.inl ⟨a, j⟩) z = Ca a j false * z (.inl a) + Ca a j true * z (.inr (.inl a)) := by
  simp [Lall]

lemma Lall_f (tail head : A → V) (m : ℕ) (C : Fin m → Option V → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) (i : Fin m) (z : Iota V A → ℝ) :
    Lall tail head m C ma Ca (.inr (.inl i)) z =
      C i none * z (.inr (.inr none)) + ∑ v, C i (some v) * z (.inr (.inr (some v))) := by
  simp [Lall, LinearMap.sum_apply]

lemma Lall_e1 (tail head : A → V) (m : ℕ) (C : Fin m → Option V → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) (v : V) (z : Iota V A → ℝ) :
    Lall tail head m C ma Ca (.inr (.inr (.inl v))) z =
      z (.inr (.inr (some v))) - Boundary tail head (fun a => z (.inl a)) v := by
  simp [Lall, Lbd_apply]

lemma Lall_e2 (tail head : A → V) (m : ℕ) (C : Fin m → Option V → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) (v : V) (z : Iota V A → ℝ) :
    Lall tail head m C ma Ca (.inr (.inr (.inr v))) z =
      Boundary tail head (fun a => z (.inl a)) v - z (.inr (.inr (some v))) := by
  simp [Lall, Lbd_apply]


lemma sum_update_mul_sub (g w : A → ℝ) (a : A) (u : ℝ) :
    ∑ x, Function.update g a u x * w x - ∑ x, g x * w x = (u - g a) * w a := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
  · simp; ring
  · intro b _ hb; simp [Function.update_of_ne hb]
  · simp

lemma sum_update_sub (g : A → ℝ) (a : A) (u : ℝ) :
    ∑ x, Function.update g a u x - ∑ x, g x = u - g a := by
  have := sum_update_mul_sub g (fun _ => 1) a u
  simpa using this

lemma feas_vals (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) (hfeas : FeasibleFlowMCFP3 tail head fa f xi) :
    ∃ u : A → ℝ, ∃ w : ℝ, (∀ a, fa a (xi a) = (u a : WithTop ℝ)) ∧
      f (Boundary tail head xi) = (w : WithTop ℝ) :=
  ⟨fun a => (fa a (xi a)).untop (hfeas.1 a), (f _).untop hfeas.2,
    fun a => (WithTop.coe_untop _ _).symm, (WithTop.coe_untop _ _).symm⟩

lemma gam_eq (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) (u : A → ℝ) (w : ℝ) (hu : ∀ a, fa a (xi a) = (u a : WithTop ℝ))
    (hw : f (Boundary tail head xi) = (w : WithTop ℝ)) :
    Gamma3 tail head fa f xi = ((∑ a, u a + w : ℝ) : WithTop ℝ) := by
  unfold Gamma3
  simp only [hu, hw]
  push_cast
  rfl

lemma pot_ineq (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (p : V → ℝ) (xi xi' u u' : A → ℝ) (w w' : ℝ)
    (hu : ∀ a, fa a (xi a) = (u a : WithTop ℝ)) (hu' : ∀ a, fa a (xi' a) = (u' a : WithTop ℝ))
    (hw : f (Boundary tail head xi) = (w : WithTop ℝ))
    (hw' : f (Boundary tail head xi') = (w' : WithTop ℝ))
    (hp : IsOptimalPotential tail head fa f xi p) :
    (∀ a, u a + Coboundary tail head p a * xi a ≤ u' a + Coboundary tail head p a * xi' a) ∧
      w - ∑ v, p v * Boundary tail head xi v ≤ w' - ∑ v, p v * Boundary tail head xi' v := by
  constructor
  · intro a
    have := hp.1 a (xi' a)
    simp only [ReducedArcCost, hu, hu'] at this
    exact_mod_cast this
  · have := hp.2 (Boundary tail head xi')
    simp only [ReducedBoundaryCost, hw, hw'] at this
    exact_mod_cast this

lemma easy_dir (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) (p : V → ℝ) (hfeas : FeasibleFlowMCFP3 tail head fa f xi)
    (hp : IsOptimalPotential tail head fa f xi p) : OptimalFlowMCFP3 tail head fa f xi := by
  refine ⟨hfeas, fun xi' hf' => ?_⟩
  obtain ⟨u, w, hu, hw⟩ := feas_vals tail head fa f xi hfeas
  obtain ⟨u', w', hu', hw'⟩ := feas_vals tail head fa f xi' hf'
  obtain ⟨h1, h2⟩ := pot_ineq tail head fa f p xi xi' u u' w w' hu hu' hw hw' hp
  rw [gam_eq tail head fa f xi u w hu hw, gam_eq tail head fa f xi' u' w' hu' hw', WithTop.coe_le_coe]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => h1 a)
  simp only [Finset.sum_add_distrib] at hs
  have e1 := bnd_pair tail head p xi
  have e2 := bnd_pair tail head p xi'
  have e3 : ∑ a, Coboundary tail head p a * xi a = ∑ a, xi a * Coboundary tail head p a :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have e4 : ∑ a, Coboundary tail head p a * xi' a = ∑ a, xi' a * Coboundary tail head p a :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  linarith

lemma transfer_dir (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) (p : V → ℝ) (ho : OptimalFlowMCFP3 tail head fa f xi)
    (hp : IsOptimalPotential tail head fa f xi p) (xi' : A → ℝ)
    (ho' : OptimalFlowMCFP3 tail head fa f xi') : IsOptimalPotential tail head fa f xi' p := by
  obtain ⟨u, w, hu, hw⟩ := feas_vals tail head fa f xi ho.1
  obtain ⟨u', w', hu', hw'⟩ := feas_vals tail head fa f xi' ho'.1
  obtain ⟨h1, h2⟩ := pot_ineq tail head fa f p xi xi' u u' w w' hu hu' hw hw' hp
  have g1 := ho.2 xi' ho'.1
  have g2 := ho'.2 xi ho.1
  rw [gam_eq tail head fa f xi u w hu hw, gam_eq tail head fa f xi' u' w' hu' hw',
    WithTop.coe_le_coe] at g1 g2
  have e1 := bnd_pair tail head p xi
  have e2 := bnd_pair tail head p xi'
  have hS : ∑ a, ((u' a + Coboundary tail head p a * xi' a) -
      (u a + Coboundary tail head p a * xi a)) =
      (∑ a, u' a + ∑ a, xi' a * Coboundary tail head p a) -
        (∑ a, u a + ∑ a, xi a * Coboundary tail head p a) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have e3 : ∑ a, Coboundary tail head p a * xi a = ∑ a, xi a * Coboundary tail head p a :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    have e4 : ∑ a, Coboundary tail head p a * xi' a = ∑ a, xi' a * Coboundary tail head p a :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [e3, e4]
  have hnn : ∀ a ∈ Finset.univ, 0 ≤ (u' a + Coboundary tail head p a * xi' a) -
      (u a + Coboundary tail head p a * xi a) := fun a _ => by linarith [h1 a]
  have hS0 : ∑ a, ((u' a + Coboundary tail head p a * xi' a) -
      (u a + Coboundary tail head p a * xi a)) = 0 := by
    have := Finset.sum_nonneg hnn
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hS0
  constructor
  · intro a t
    have heq : ReducedArcCost tail head fa p a (xi' a) = ReducedArcCost tail head fa p a (xi a) := by
      simp only [ReducedArcCost, hu, hu']
      have := hz a (Finset.mem_univ a)
      have h' : u' a + Coboundary tail head p a * xi' a = u a + Coboundary tail head p a * xi a := by
        linarith
      exact_mod_cast congrArg (fun x : ℝ => (x : WithTop ℝ)) h'
    rw [heq]; exact hp.1 a t
  · intro y
    have heq : ReducedBoundaryCost f p (Boundary tail head xi') =
        ReducedBoundaryCost f p (Boundary tail head xi) := by
      simp only [ReducedBoundaryCost, hw, hw']
      have := Finset.sum_nonneg hnn
      have h' : w' - ∑ v, p v * Boundary tail head xi' v = w - ∑ v, p v * Boundary tail head xi v := by
        linarith
      exact_mod_cast congrArg (fun x : ℝ => (x : WithTop ℝ)) h'
    rw [heq]; exact hp.2 y


theorem hard_core (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (m : ℕ) (C : Fin m → Option V → ℝ) (B : Fin m → ℝ) (ma : A → ℕ)
    (Ca : ∀ a, Fin (ma a) → Bool → ℝ) (Ba : ∀ a, Fin (ma a) → ℝ)
    (hC : ∀ (y : V → ℝ) (r : ℝ), f y ≤ (r : WithTop ℝ) ↔
      ∀ i, C i none * r + ∑ v, C i (some v) * y v ≤ B i)
    (hCa : ∀ a (t s : ℝ), fa a t ≤ (s : WithTop ℝ) ↔
      ∀ j, Ca a j false * t + Ca a j true * s ≤ Ba a j)
    (xi : A → ℝ) (hopt : OptimalFlowMCFP3 tail head fa f xi) :
    ∃ p, IsOptimalPotential tail head fa f xi p := by
  obtain ⟨hfeas, hmin⟩ := hopt
  have lp_flow : ∀ z : Iota V A → ℝ, (∀ k, Lall tail head m C ma Ca k z ≤ ball m B ma Ba k) →
      FeasibleFlowMCFP3 tail head fa f (fun a => z (.inl a)) ∧
      Gamma3 tail head fa f (fun a => z (.inl a)) ≤ ((cobj z : ℝ) : WithTop ℝ) := by
    intro z hz
    have harc : ∀ a, fa a (z (.inl a)) ≤ ((z (.inr (.inl a)) : ℝ) : WithTop ℝ) := by
      intro a; rw [hCa]; intro j; have := hz (.inl ⟨a, j⟩)
      rw [Lall_arc] at this; simp only [ball] at this; linarith
    have hy : (fun v => z (.inr (.inr (some v)))) = Boundary tail head (fun a => z (.inl a)) := by
      funext v
      have h1 := hz (.inr (.inr (.inl v))); have h2 := hz (.inr (.inr (.inr v)))
      rw [Lall_e1] at h1; rw [Lall_e2] at h2
      simp only [ball] at h1 h2; linarith
    have hfz : f (Boundary tail head (fun a => z (.inl a))) ≤
        ((z (.inr (.inr none)) : ℝ) : WithTop ℝ) := by
      rw [← hy, hC]; intro i; have := hz (.inr (.inl i))
      rw [Lall_f] at this; simp only [ball] at this; linarith
    refine ⟨⟨fun a => ne_top_of_le_ne_top WithTop.coe_ne_top (harc a),
      ne_top_of_le_ne_top WithTop.coe_ne_top hfz⟩, ?_⟩
    rw [cobj_apply]; unfold Gamma3
    push_cast
    exact add_le_add (Finset.sum_le_sum (fun a _ => harc a)) hfz
  obtain ⟨sS, rS, hsS, hrS⟩ := feas_vals tail head fa f xi hfeas
  set zS : Iota V A → ℝ := mkv xi sS (Boundary tail head xi) rS with hzSdef
  have hzS : ∀ k, Lall tail head m C ma Ca k zS ≤ ball m B ma Ba k := by
    rintro (⟨a, j⟩ | i | v | v)
    · rw [Lall_arc]; simp only [zS, mkv, ball]
      have := (hCa a _ _).1 (le_of_eq (hsS a)) j; linarith
    · rw [Lall_f]; simp only [zS, mkv, ball]
      have := (hC _ _).1 (le_of_eq hrS) i; linarith
    · rw [Lall_e1]; simp [zS, mkv, ball]
    · rw [Lall_e2]; simp [zS, mkv, ball]
  have hgam : Gamma3 tail head fa f xi = ((cobj zS : ℝ) : WithTop ℝ) := by
    rw [gam_eq tail head fa f xi sS rS hsS hrS, cobj_apply]
    simp [zS, mkv]
  have hnoimp : ∀ d, (∀ k, (if Lall tail head m C ma Ca k zS = ball m B ma Ba k
      then Lall tail head m C ma Ca k else 0) d ≤ 0) → 0 ≤ (cobj : (Iota V A → ℝ) →ₗ[ℝ] ℝ) d := by
    intro d hd
    by_contra hneg; push_neg at hneg
    have hev : ∀ k, ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
        Lall tail head m C ma Ca k (zS + ε • d) ≤ ball m B ma Ba k := by
      intro k
      have hlin : ∀ ε : ℝ, Lall tail head m C ma Ca k (zS + ε • d) =
          Lall tail head m C ma Ca k zS + ε * Lall tail head m C ma Ca k d := by
        intro ε; simp [map_add, map_smul]
      simp_rw [hlin]
      by_cases hk : Lall tail head m C ma Ca k zS = ball m B ma Ba k
      · have := hd k; rw [if_pos hk] at this
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [hk]; nlinarith [Set.mem_Ioi.mp hε]
      · have hlt : Lall tail head m C ma Ca k zS < ball m B ma Ba k := lt_of_le_of_ne (hzS k) hk
        have hc : Continuous (fun ε : ℝ => Lall tail head m C ma Ca k zS +
            ε * Lall tail head m C ma Ca k d) := by fun_prop
        have ht := hc.tendsto 0
        simp only [zero_mul, add_zero] at ht
        exact ((ht.eventually (gt_mem_nhds hlt)).mono fun ε h => h.le).filter_mono
          nhdsWithin_le_nhds
    have hall := Filter.eventually_all.2 hev
    obtain ⟨ε, hε, hεpos⟩ := (hall.and self_mem_nhdsWithin).exists
    obtain ⟨hF, hG⟩ := lp_flow _ hε
    have h1 := hmin _ hF
    have hxi : (fun a => (zS + ε • d) (.inl a)) = fun a => xi a + ε * d (.inl a) := by
      funext a; simp [zS, mkv]
    rw [hgam] at h1
    have h2 := h1.trans hG
    rw [WithTop.coe_le_coe, map_add, map_smul, smul_eq_mul] at h2
    have hε0 : (0:ℝ) < ε := hεpos
    nlinarith
  obtain ⟨lam, hlam0, hid⟩ := farkasL _ _ hnoimp
  set lam' : Kap V A m ma → ℝ := fun k =>
    if Lall tail head m C ma Ca k zS = ball m B ma Ba k then lam k else 0 with hlam'
  have hid' : ∀ z, (cobj : (Iota V A → ℝ) →ₗ[ℝ] ℝ) z =
      - ∑ k, lam' k * Lall tail head m C ma Ca k z := by
    intro z; rw [hid z]; congr 1; refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : Lall tail head m C ma Ca k zS = ball m B ma Ba k <;> simp [lam', hk]
  have hl0 : ∀ k, 0 ≤ lam' k := by
    intro k; by_cases hk : Lall tail head m C ma Ca k zS = ball m B ma Ba k <;>
      simp [lam', hk, hlam0 k]
  have hact : ∀ k, lam' k ≠ 0 → Lall tail head m C ma Ca k zS = ball m B ma Ba k := by
    intro k hk; by_contra h; exact hk (by simp [lam', h])
  have key : ∀ z : Iota V A → ℝ,
      (∀ x, Lall tail head m C ma Ca (Sum.inl x : Kap V A m ma) z ≤
        ball m B ma Ba (Sum.inl x : Kap V A m ma)) →
      (∀ i, Lall tail head m C ma Ca (Sum.inr (Sum.inl i) : Kap V A m ma) z ≤
        ball m B ma Ba (Sum.inr (Sum.inl i) : Kap V A m ma)) →
      cobj zS - cobj z ≤
        ∑ v, lam' (.inr (.inr (.inl v))) * (Lall tail head m C ma Ca (.inr (.inr (.inl v))) z -
          Lall tail head m C ma Ca (.inr (.inr (.inl v))) zS) +
        ∑ v, lam' (.inr (.inr (.inr v))) * (Lall tail head m C ma Ca (.inr (.inr (.inr v))) z -
          Lall tail head m C ma Ca (.inr (.inr (.inr v))) zS) := by
    intro z hz1 hz2
    have he : cobj zS - cobj z = ∑ k, lam' k * (Lall tail head m C ma Ca k z -
        Lall tail head m C ma Ca k zS) := by
      rw [hid', hid']; simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [he, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have hterm : ∀ k, Lall tail head m C ma Ca k z ≤ ball m B ma Ba k →
        lam' k * (Lall tail head m C ma Ca k z - Lall tail head m C ma Ca k zS) ≤ 0 := by
      intro k hk
      by_cases h0 : lam' k = 0
      · simp [h0]
      · rw [hact k h0]; exact mul_nonpos_of_nonneg_of_nonpos (hl0 k) (by linarith)
    have e1 := Finset.sum_nonpos (fun x (_ : x ∈ Finset.univ) => hterm _ (hz1 x))
    have e2 := Finset.sum_nonpos (fun x (_ : x ∈ Finset.univ) => hterm _ (hz2 x))
    linarith
  refine ⟨fun v => lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v))), ?_, ?_⟩
  · intro a t
    simp only [ReducedArcCost]
    rw [hsS a]
    cases hft : fa a t with
    | top => simp
    | coe s =>
      set z : Iota V A → ℝ := mkv (Function.update xi a t) (Function.update sS a s)
        (Boundary tail head xi) rS with hzdef
      have hk := key z (by
        rintro ⟨a', j⟩
        rw [Lall_arc]; simp only [ball]
        by_cases ha : a' = a
        · subst ha
          simp only [z, mkv, Function.update_self]
          have := (hCa a' t s).1 (le_of_eq hft) j; linarith
        · simp only [z, mkv, Function.update_of_ne ha]
          have := hzS (.inl ⟨a', j⟩); rw [Lall_arc] at this; simpa [zS, mkv, ball] using this)
        (by
          intro i
          have := hzS (.inr (.inl i)); rw [Lall_f] at this ⊢; simpa [z, zS, mkv] using this)
      simp only [Lall_e1, Lall_e2, cobj_apply, z, zS, mkv] at hk
      have hc : ∑ x, Function.update sS a s x - ∑ x, sS x = s - sS a := sum_update_sub sS a s
      have hb : ∑ v, (lam' (.inr (.inr (.inl v))) *
            (Boundary tail head xi v - Boundary tail head (fun a_1 => Function.update xi a t a_1) v -
              (Boundary tail head xi v - Boundary tail head xi v)) +
          lam' (.inr (.inr (.inr v))) *
            (Boundary tail head (fun a_1 => Function.update xi a t a_1) v - Boundary tail head xi v -
              (Boundary tail head xi v - Boundary tail head xi v))) =
          ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) *
            Boundary tail head (Function.update xi a t) v -
          ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) *
            Boundary tail head xi v := by
        rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun v _ => ?_); ring
      rw [← Finset.sum_add_distrib, hb, bnd_pair, bnd_pair,
        sum_update_mul_sub] at hk
      have : sS a + Coboundary tail head
          (fun v => lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) a * xi a ≤
          s + Coboundary tail head
          (fun v => lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) a * t := by
        nlinarith
      exact_mod_cast this
  · intro y
    simp only [ReducedBoundaryCost]
    rw [hrS]
    cases hfy : f y with
    | top => simp
    | coe r =>
      set z : Iota V A → ℝ := mkv xi sS y r with hzdef
      have hk := key z (by
        rintro ⟨a', j⟩
        have := hzS (.inl ⟨a', j⟩); rw [Lall_arc] at this ⊢; simpa [z, zS, mkv] using this)
        (by
          intro i
          rw [Lall_f]; simp only [ball, z, mkv]
          have := (hC y r).1 (le_of_eq hfy) i; linarith)
      simp only [Lall_e1, Lall_e2, cobj_apply, z, zS, mkv] at hk
      rw [← Finset.sum_add_distrib] at hk
      have hb : ∑ v, (lam' (.inr (.inr (.inl v))) *
            (y v - Boundary tail head xi v - (Boundary tail head xi v - Boundary tail head xi v)) +
          lam' (.inr (.inr (.inr v))) *
            (Boundary tail head xi v - y v - (Boundary tail head xi v - Boundary tail head xi v))) =
          ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) *
            Boundary tail head xi v -
          ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) * y v := by
        rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun v _ => ?_); ring
      rw [hb] at hk
      have : rS - ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) *
            Boundary tail head xi v ≤
          r - ∑ v, (lam' (.inr (.inr (.inr v))) - lam' (.inr (.inr (.inl v)))) * y v := by
        linarith
      exact_mod_cast this


theorem potential_criterion_mcfp3_core (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (hf : IsPolyhedralConvex f) (hfa : ∀ a, IsPolyhedralConvexArc (fa a)) :
    (∀ xi, FeasibleFlowMCFP3 tail head fa f xi →
      (OptimalFlowMCFP3 tail head fa f xi ↔ ∃ p : V → ℝ, IsOptimalPotential tail head fa f xi p)) ∧
    (∀ xi p, OptimalFlowMCFP3 tail head fa f xi → IsOptimalPotential tail head fa f xi p →
      ∀ xi', FeasibleFlowMCFP3 tail head fa f xi' →
        (OptimalFlowMCFP3 tail head fa f xi' ↔ IsOptimalPotential tail head fa f xi' p)) := by
  obtain ⟨m, C, B, hS⟩ := hf
  choose ma Ca Ba hSa using hfa
  have hC : ∀ (y : V → ℝ) (r : ℝ), f y ≤ (r : WithTop ℝ) ↔
      ∀ i, C i none * r + ∑ v, C i (some v) * y v ≤ B i := by
    intro y r
    have := Set.ext_iff.mp hS (fun o => Option.elim o r y)
    simpa [Fintype.sum_option] using this
  have hCa : ∀ a (t s : ℝ), fa a t ≤ (s : WithTop ℝ) ↔
      ∀ j, Ca a j false * t + Ca a j true * s ≤ Ba a j := by
    intro a t s
    have := Set.ext_iff.mp (hSa a) (fun b => cond b s t)
    simp only [Set.mem_setOf_eq, Fintype.sum_bool, cond_true, cond_false] at this
    rw [this]
    exact forall_congr' (fun j => by rw [add_comm])
  refine ⟨fun xi hfe => ⟨fun ho => hard_core tail head fa f m C B ma Ca Ba hC hCa xi ho,
    fun ⟨p, hp⟩ => easy_dir tail head fa f xi p hfe hp⟩,
    fun xi p ho hp xi' hf' => ⟨fun ho' => transfer_dir tail head fa f xi p ho hp xi' ho',
      fun hp' => easy_dir tail head fa f xi' p hf' hp'⟩⟩

end PC

section MCFP0Pot
set_option linter.unusedSectionVars false

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma top_sub_coe' (s : ℝ) : (⊤ : WithTop ℝ) - (s : WithTop ℝ) = ⊤ := by
  simp

lemma coe_sub_coe' (r s : ℝ) : ((r : WithTop ℝ) - (s : WithTop ℝ)) = ((r - s : ℝ) : WithTop ℝ) := by
  simp

/-- Arc cost of MCFP0 is polyhedral convex. -/
lemma arc0_poly (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (gamma : A → ℝ) (a : A) :
    IsPolyhedralConvexArc (ArcCostMCFP0 cUpper cLower gamma a) := by
  unfold IsPolyhedralConvexArc
  -- three constraints
  let a0 : Fin 3 → Bool → ℝ := fun i w =>
    match i with
    | 0 => if w then -1 else gamma a
    | 1 => match cUpper a with
      | ⊤ => 0
      | (_ : ℝ) => if w then 0 else 1
    | 2 => match cLower a with
      | ⊥ => 0
      | (_ : ℝ) => if w then 0 else -1
  let b0 : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 0
    | 1 => match cUpper a with
      | ⊤ => 0
      | (r : ℝ) => r
    | 2 => match cLower a with
      | ⊥ => 0
      | (r : ℝ) => -r
  have h := isPolyhedron_of_fintype a0 b0
  convert h using 1
  ext p
  simp only [Set.mem_setOf_eq, Fintype.sum_bool]
  unfold ArcCostMCFP0
  constructor
  · intro hle i
    have hbox : cLower a ≤ ((p false : ℝ) : WithBot ℝ) ∧ ((p false : ℝ) : WithTop ℝ) ≤ cUpper a := by
      by_contra hc
      rw [if_neg hc] at hle
      exact absurd hle (by simp)
    rw [if_pos hbox, WithTop.coe_le_coe] at hle
    obtain ⟨cu, hcu⟩ : ∃ cu, cUpper a = cu := ⟨_, rfl⟩
    obtain ⟨cl, hcl⟩ : ∃ cl, cLower a = cl := ⟨_, rfl⟩
    rw [hcu, hcl] at hbox
    fin_cases i
    · simp [a0, b0]; linarith
    · simp only [a0, b0, hcu]
      induction cu using WithTop.recTopCoe with
      | top => simp
      | coe r =>
        simp only [WithTop.coe_le_coe] at hbox
        simp; linarith [hbox.2]
    · simp only [a0, b0, hcl]
      induction cl using WithBot.recBotCoe with
      | bot => simp
      | coe r =>
        simp only [WithBot.coe_le_coe] at hbox
        simp; linarith [hbox.1]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [a0, b0] at h0 h1 h2
    obtain ⟨cu, hcu⟩ : ∃ cu, cUpper a = cu := ⟨_, rfl⟩
    obtain ⟨cl, hcl⟩ : ∃ cl, cLower a = cl := ⟨_, rfl⟩
    rw [hcu] at h1; rw [hcl] at h2
    have hbox : cLower a ≤ ((p false : ℝ) : WithBot ℝ) ∧ ((p false : ℝ) : WithTop ℝ) ≤ cUpper a := by
      rw [hcu, hcl]
      constructor
      · induction cl using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe r =>
          simp at h2
          exact WithBot.coe_le_coe.2 (by linarith)
      · induction cu using WithTop.recTopCoe with
        | top => exact le_top
        | coe r =>
          simp at h1
          exact WithTop.coe_le_coe.2 (by linarith)
    rw [if_pos hbox, WithTop.coe_le_coe]
    simp at h0; linarith

/-- Boundary cost of MCFP0 is polyhedral convex. -/
lemma bnd0_poly (x : V → ℝ) : IsPolyhedralConvex (BoundaryCostMCFP0 x) := by
  unfold IsPolyhedralConvex
  let a0 : V ⊕ V ⊕ Unit → Option V → ℝ := fun i w =>
    match i with
    | .inl v => if w = some v then 1 else 0
    | .inr (.inl v) => if w = some v then -1 else 0
    | .inr (.inr _) => if w = none then -1 else 0
  let b0 : V ⊕ V ⊕ Unit → ℝ := fun i =>
    match i with
    | .inl v => x v
    | .inr (.inl v) => - x v
    | .inr (.inr _) => 0
  have h := isPolyhedron_of_fintype a0 b0
  convert h using 1
  ext p
  simp only [Set.mem_setOf_eq]
  unfold BoundaryCostMCFP0
  have hs1 : ∀ v, ∑ w : Option V, (if w = some v then (1:ℝ) else 0) * p w = p (some v) := by
    intro v; simp [ite_mul]
  have hs2 : ∀ v, ∑ w : Option V, (if w = some v then (-1:ℝ) else 0) * p w = - p (some v) := by
    intro v; simp [ite_mul]
  have hs3 : ∑ w : Option V, (if w = none then (-1:ℝ) else 0) * p w = - p none := by
    simp [ite_mul]
  constructor
  · intro hle i
    have heq : (fun v => p (some v)) = x := by
      by_contra hc
      rw [if_neg hc] at hle
      exact absurd hle (by simp)
    rw [if_pos heq] at hle
    have hle' : (0:ℝ) ≤ p none := by exact_mod_cast hle
    rcases i with v | v | u
    · simp only [a0, b0, hs1]; exact (congrFun heq v).le
    · simp only [a0, b0, hs2]; linarith [(congrFun heq v).ge]
    · simp only [a0, b0, hs3]; linarith
  · intro h
    have heq : (fun v => p (some v)) = x := by
      funext v
      have h1 := h (.inl v)
      have h2 := h (.inr (.inl v))
      simp only [a0, b0, hs1, hs2] at h1 h2
      linarith
    rw [if_pos heq]
    have h3 := h (.inr (.inr ()))
    simp only [a0, b0, hs3] at h3
    exact_mod_cast (by linarith : (0:ℝ) ≤ p none)

/-- Conditions and data of the difference-constraint description of optimal potentials. -/
def Q0 (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (xi0 : A → ℝ) : A ⊕ A → Prop
  | .inl a => ((xi0 a : ℝ) : WithTop ℝ) < cUpper a
  | .inr a => cLower a < ((xi0 a : ℝ) : WithBot ℝ)

def u0 (tail head : A → V) : A ⊕ A → V
  | .inl a => head a
  | .inr a => tail a

def v0 (tail head : A → V) : A ⊕ A → V
  | .inl a => tail a
  | .inr a => head a

def c0 (gamma : A → ℝ) : A ⊕ A → ℝ
  | .inl a => gamma a
  | .inr a => -gamma a

lemma rac_eq (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (p : V → ℝ) (a : A) (t : ℝ) :
    ReducedArcCost tail head (ArcCostMCFP0 cUpper cLower gamma) p a t =
      if cLower a ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ cUpper a then
        (((gamma a + Coboundary tail head p a) * t : ℝ) : WithTop ℝ) else ⊤ := by
  unfold ReducedArcCost ArcCostMCFP0
  split_ifs with h
  · rw [← WithTop.coe_add]; congr 1; ring
  · simp

lemma feas0_iff' (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ) :
    FeasibleFlowMCFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi ↔
      (∀ a, cLower a ≤ (xi a : WithBot ℝ) ∧ (xi a : WithTop ℝ) ≤ cUpper a) ∧
        Boundary tail head xi = x := by
  unfold FeasibleFlowMCFP3 ArcCostMCFP0 BoundaryCostMCFP0
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => ?_, ?_⟩
    · have := h1 a; by_contra hc; exact this (if_neg hc)
    · by_contra hc; exact h2 (if_neg hc)
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by rw [if_pos (h1 a)]; exact WithTop.coe_ne_top, by
      rw [if_pos h2]; exact WithTop.zero_ne_top⟩

lemma gam0' (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi : A → ℝ)
    (h : FeasibleFlowMCFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi) :
    Gamma3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi =
      ((∑ a, gamma a * xi a : ℝ) : WithTop ℝ) := by
  rw [feas0_iff'] at h
  unfold Gamma3 ArcCostMCFP0 BoundaryCostMCFP0
  rw [if_pos h.2, add_zero]
  push_cast
  exact Finset.sum_congr rfl (fun a _ => by rw [if_pos (h.1 a)])

lemma argmin_arc_iff (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (p : V → ℝ) (a : A) (t0 : ℝ)
    (hbox : cLower a ≤ (t0 : WithBot ℝ) ∧ (t0 : WithTop ℝ) ≤ cUpper a) :
    t0 ∈ ArgMinArc (ReducedArcCost tail head (ArcCostMCFP0 cUpper cLower gamma) p a) ↔
      (((t0 : ℝ) : WithTop ℝ) < cUpper a → 0 ≤ gamma a + Coboundary tail head p a) ∧
      (cLower a < ((t0 : ℝ) : WithBot ℝ) → gamma a + Coboundary tail head p a ≤ 0) := by
  set s := gamma a + Coboundary tail head p a with hs
  simp only [ArgMinArc, Set.mem_setOf_eq, rac_eq, if_pos hbox]
  constructor
  · intro h
    constructor
    · intro hlt
      by_contra hneg
      push_neg at hneg
      -- pick t' > t0 within the box
      obtain ⟨t', ht'0, ht'box⟩ : ∃ t', t0 < t' ∧
          cLower a ≤ (t' : WithBot ℝ) ∧ (t' : WithTop ℝ) ≤ cUpper a := by
        obtain ⟨cu, hcu⟩ : ∃ cu, cUpper a = cu := ⟨_, rfl⟩
        rw [hcu] at hlt hbox ⊢
        induction cu using WithTop.recTopCoe with
        | top =>
          exact ⟨t0 + 1, by linarith, le_trans hbox.1 (WithBot.coe_le_coe.2 (by linarith)), le_top⟩
        | coe r =>
          have : t0 < r := WithTop.coe_lt_coe.1 hlt
          exact ⟨r, this, le_trans hbox.1 (WithBot.coe_le_coe.2 this.le), le_rfl⟩
      have := h t'
      rw [if_pos ht'box, WithTop.coe_le_coe] at this
      nlinarith
    · intro hlt
      by_contra hneg
      push_neg at hneg
      obtain ⟨t', ht'0, ht'box⟩ : ∃ t', t' < t0 ∧
          cLower a ≤ (t' : WithBot ℝ) ∧ (t' : WithTop ℝ) ≤ cUpper a := by
        obtain ⟨cl, hcl⟩ : ∃ cl, cLower a = cl := ⟨_, rfl⟩
        rw [hcl] at hlt hbox ⊢
        induction cl using WithBot.recBotCoe with
        | bot =>
          exact ⟨t0 - 1, by linarith, bot_le, le_trans (WithTop.coe_le_coe.2 (by linarith)) hbox.2⟩
        | coe r =>
          have : r < t0 := WithBot.coe_lt_coe.1 hlt
          exact ⟨r, this, le_rfl, le_trans (WithTop.coe_le_coe.2 this.le) hbox.2⟩
      have := h t'
      rw [if_pos ht'box, WithTop.coe_le_coe] at this
      nlinarith
  · rintro ⟨h1, h2⟩ t'
    split_ifs with hb
    · rw [WithTop.coe_le_coe]
      rcases lt_trichotomy t0 t' with hlt | heq | hgt
      · have : ((t0 : ℝ) : WithTop ℝ) < cUpper a :=
          lt_of_lt_of_le (WithTop.coe_lt_coe.2 hlt) hb.2
        have := h1 this
        nlinarith
      · rw [heq]
      · have : cLower a < ((t0 : ℝ) : WithBot ℝ) :=
          lt_of_le_of_lt hb.1 (WithBot.coe_lt_coe.2 hgt)
        have := h2 this
        nlinarith
    · exact le_top

lemma pot0_iff (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi0 : A → ℝ)
    (hfe : FeasibleFlowMCFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi0)
    (p : V → ℝ) :
    IsOptimalPotential tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi0 p ↔
      p ∈ DiffSet (Q0 cUpper cLower xi0) (u0 tail head) (v0 tail head) (c0 gamma) := by
  rw [feas0_iff'] at hfe
  unfold IsOptimalPotential
  have hbd : Boundary tail head xi0 ∈
      ArgMinR (ReducedBoundaryCost (BoundaryCostMCFP0 x) p) := by
    intro q
    unfold ReducedBoundaryCost BoundaryCostMCFP0
    rw [if_pos hfe.2]
    by_cases hq : q = x
    · rw [if_pos hq, hfe.2, hq]
    · rw [if_neg hq, top_sub_coe']; exact le_top
  simp only [hbd, and_true]
  constructor
  · intro h i
    rcases i with a | a
    · intro hQ
      have := ((argmin_arc_iff tail head cUpper cLower gamma p a (xi0 a) (hfe.1 a)).1 (h a)).1 hQ
      simp only [u0, v0, c0, Coboundary] at this ⊢
      linarith
    · intro hQ
      have := ((argmin_arc_iff tail head cUpper cLower gamma p a (xi0 a) (hfe.1 a)).1 (h a)).2 hQ
      simp only [u0, v0, c0, Coboundary] at this ⊢
      linarith
  · intro h a
    rw [argmin_arc_iff tail head cUpper cLower gamma p a (xi0 a) (hfe.1 a)]
    constructor
    · intro hQ
      have := h (.inl a) hQ
      simp only [u0, v0, c0, Coboundary] at this ⊢
      linarith
    · intro hQ
      have := h (.inr a) hQ
      simp only [u0, v0, c0, Coboundary] at this ⊢
      linarith

lemma potset0_eq (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi0 : A → ℝ)
    (hopt : OptimalFlowMCFP0 tail head cUpper cLower gamma x xi0) :
    OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x =
      DiffSet (Q0 cUpper cLower xi0) (u0 tail head) (v0 tail head) (c0 gamma) := by
  have hcore := potential_criterion_mcfp3_core tail head (ArcCostMCFP0 cUpper cLower gamma)
    (BoundaryCostMCFP0 x) (bnd0_poly x) (arc0_poly cUpper cLower gamma)
  unfold OptimalFlowMCFP0 at hopt
  ext p
  unfold OptimalPotentialSetMCFP0 OptimalPotentialSetMSFP3
  simp only [Set.mem_setOf_eq]
  rw [← pot0_iff tail head cUpper cLower gamma x xi0 hopt.1 p]
  constructor
  · rintro ⟨xi, hxi, hp⟩
    exact (hcore.2 xi p hxi hp xi0 hopt.1).1 hopt
  · intro hp
    exact ⟨xi0, hopt, hp⟩

lemma potset0_nonempty (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (xi0 : A → ℝ)
    (hopt : OptimalFlowMCFP0 tail head cUpper cLower gamma x xi0) :
    (OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x).Nonempty := by
  have hcore := potential_criterion_mcfp3_core tail head (ArcCostMCFP0 cUpper cLower gamma)
    (BoundaryCostMCFP0 x) (bnd0_poly x) (arc0_poly cUpper cLower gamma)
  unfold OptimalFlowMCFP0 at hopt
  obtain ⟨p, hp⟩ := (hcore.1 xi0 hopt.1).1 hopt
  exact ⟨p, xi0, hopt, hp⟩

theorem dual_part (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (hopt : ∃ xi, OptimalFlowMCFP0 tail head cUpper cLower gamma x xi) :
    LConvexPolyhedronR (OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) ∧
    ((∀ a, ∃ n : ℤ, gamma a = (n:ℝ)) →
      IsIntegralPolyhedron (OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) ∧
      ∃ pZ : V → ℤ, (fun v => (pZ v : ℝ)) ∈ OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) := by
  obtain ⟨xi0, hopt⟩ := hopt
  have hne := potset0_nonempty tail head cUpper cLower gamma x xi0 hopt
  rw [potset0_eq tail head cUpper cLower gamma x xi0 hopt] at hne ⊢
  refine ⟨⟨diffSet_polyhedron _ _ _ _, hne, fun p hp q hq => ⟨diffSet_sup _ _ _ _ hp hq,
    diffSet_inf _ _ _ _ hp hq⟩, fun p hp α => diffSet_trans _ _ _ _ hp α⟩, fun hg => ?_⟩
  have hc : ∀ i, ∃ n : ℤ, c0 gamma i = n := by
    intro i
    rcases i with a | a
    · obtain ⟨n, hn⟩ := hg a; exact ⟨n, by simp [c0, hn]⟩
    · obtain ⟨n, hn⟩ := hg a; exact ⟨-n, by simp [c0, hn]⟩
  refine ⟨diffSet_integral _ _ _ _ hc, ?_⟩
  obtain ⟨p, hp⟩ := hne
  exact ⟨fun v => ⌊p v⌋, diffSet_floor _ _ _ _ hc hp⟩

end MCFP0Pot

section Primal
set_option linter.unusedSectionVars false

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def aT (tail head : A → V) : A ⊕ A → V
  | .inl a => tail a
  | .inr a => head a

def aH (tail head : A → V) : A ⊕ A → V
  | .inl a => head a
  | .inr a => tail a

def und : A ⊕ A → A
  | .inl a => a
  | .inr a => a

def rev : A ⊕ A → A ⊕ A
  | .inl a => .inr a
  | .inr a => .inl a

def IsCyc (tail head : A → V) (k : ℕ) (c : Fin (k+1) → A ⊕ A) : Prop :=
  ∀ i : Fin (k+1), aH tail head (c i) = aT tail head (c (i+1))

def evA : A ⊕ A → A → ℝ
  | .inl a => fun b => if a = b then 1 else 0
  | .inr a => fun b => if a = b then -1 else 0

def chiC {k : ℕ} (c : Fin (k+1) → A ⊕ A) : A → ℝ := fun b => ∑ i, evA (c i) b

lemma boundary_sum {ι : Type*} [Fintype ι] (tail head : A → V) (g : ι → A → ℝ) (v : V) :
    Boundary tail head (fun b => ∑ i, g i b) v = ∑ i, Boundary tail head (g i) v := by
  unfold Boundary; rw [Finset.sum_sub_distrib]; congr 1 <;> exact Finset.sum_comm

lemma boundary_lin (tail head : A → V) (d g : A → ℝ) (e : ℝ) (v : V) :
    Boundary tail head (fun b => d b + e * g b) v =
      Boundary tail head d v + e * Boundary tail head g v := by
  simp only [Boundary, Finset.sum_add_distrib, ← Finset.mul_sum]; ring

lemma boundary_evA (tail head : A → V) (e : A ⊕ A) (v : V) :
    Boundary tail head (evA e) v =
      (if aT tail head e = v then 1 else 0) -
        (if aH tail head e = v then 1 else 0) := by
  cases e with
  | inl a =>
    simp [Boundary, evA, aT, aH, Finset.sum_ite_eq]
    split_ifs <;> simp_all
  | inr a =>
    simp [Boundary, evA, aT, aH, Finset.sum_ite_eq]
    split_ifs <;> simp_all

lemma boundary_chi (tail head : A → V) {k : ℕ} (c : Fin (k+1) → A ⊕ A)
    (hc : IsCyc tail head k c) :
    Boundary tail head (chiC c) = 0 := by
  funext v
  unfold chiC
  rw [boundary_sum]
  simp_rw [boundary_evA]
  rw [Finset.sum_sub_distrib, Pi.zero_apply, sub_eq_zero]
  have h : ∀ i, aH tail head (c i) = aT tail head (c (i+1)) := hc
  simp_rw [h]
  exact (Fintype.sum_equiv (Equiv.addRight (1 : Fin (k+1)))
    (fun i => if aT tail head (c (i+1)) = v then (1:ℝ) else 0)
    (fun i => if aT tail head (c i) = v then (1:ℝ) else 0) (fun i => rfl)).symm

lemma evA_ne_zero {e : A ⊕ A} {b : A} (h : evA e b ≠ 0) : und e = b := by
  cases e with
  | inl a => simp only [evA] at h; split_ifs at h with h1; · exact h1
             · exact absurd rfl h
  | inr a => simp only [evA] at h; split_ifs at h with h1; · exact h1
             · exact absurd rfl h

lemma evA_und (e : A ⊕ A) : evA e (und e) ≠ 0 := by
  cases e <;> simp [evA, und]

lemma ends (tail head : A → V) (e : A ⊕ A) :
    (aT tail head e = tail (und e) ∧ aH tail head e = head (und e)) ∨
    (aT tail head e = head (und e) ∧ aH tail head e = tail (und e)) := by
  cases e with
  | inl a => left; exact ⟨rfl, rfl⟩
  | inr a => right; exact ⟨rfl, rfl⟩

lemma eq_of_und_eq {e e' : A ⊕ A} (h : und e = und e') (hr : e ≠ rev e') : e = e' := by
  cases e with
  | inl a =>
    cases e' with
    | inl a' => simp only [und] at h; rw [h]
    | inr a' => simp only [und] at h; exact absurd (by rw [h]; rfl) hr
  | inr a =>
    cases e' with
    | inl a' => simp only [und] at h; exact absurd (by rw [h]; rfl) hr
    | inr a' => simp only [und] at h; rw [h]

/-- From a "degree ≠ 1" condition on a set of arcs, extract a closed walk with nonzero
net multiplicity. -/
lemma walk_cycle (tail head : A → V) (F : Finset A) (hF : F.Nonempty)
    (hdeg : ∀ e : A ⊕ A, und e ∈ F →
      ∃ e', und e' ∈ F ∧ aT tail head e' = aH tail head e ∧ e' ≠ rev e) :
    ∃ k, ∃ c : Fin (k+1) → A ⊕ A, (∀ i, und (c i) ∈ F) ∧ IsCyc tail head k c ∧
      ∃ b, chiC c b ≠ 0 := by
  obtain ⟨b0, hb0⟩ := hF
  choose! nx hnxF hnxT hnxR using hdeg
  set e0 : A ⊕ A := .inl b0 with he0
  have hsF : ∀ m, und (nx^[m] e0) ∈ F := by
    intro m; induction m with
    | zero => exact hb0
    | succ m ihm => rw [Function.iterate_succ_apply']; exact hnxF _ ihm
  have hsT : ∀ m, aT tail head (nx^[m+1] e0) = aH tail head (nx^[m] e0) := by
    intro m; rw [Function.iterate_succ_apply']; exact hnxT _ (hsF m)
  have hsR : ∀ m, nx^[m+1] e0 ≠ rev (nx^[m] e0) := by
    intro m; rw [Function.iterate_succ_apply']; exact hnxR _ (hsF m)
  set vs : ℕ → V := fun m => aT tail head (nx^[m] e0) with hvs
  have hex : ∃ j, ∃ i, i < j ∧ vs i = vs j := by
    obtain ⟨i, j, hne, he⟩ := Finite.exists_ne_map_eq_of_infinite vs
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ⟨j, i, h, he⟩
    · exact ⟨i, j, h, he.symm⟩
  obtain ⟨i, hij, heq⟩ := Nat.find_spec hex
  set j := Nat.find hex with hj
  have hmin : ∀ l m, l < m → m < j → vs l ≠ vs m := by
    intro l m hlm hmj hv
    exact Nat.find_min hex hmj ⟨l, hlm, hv⟩
  obtain ⟨k, hk⟩ : ∃ k, j = i + k + 1 := ⟨j - i - 1, by omega⟩
  let c : Fin (k+1) → A ⊕ A := fun idx => nx^[i + idx] e0
  have hcF : ∀ idx, und (c idx) ∈ F := fun idx => hsF _
  have hcyc : IsCyc tail head k c := by
    intro idx
    simp only [c]
    rw [Fin.val_add_one]
    split_ifs with hl
    · rw [hl, Fin.val_last, add_zero]
      have : vs i = vs (i + k + 1) := by rw [← hk]; exact heq
      simp only [hvs] at this
      rw [this]
      exact (hsT _).symm
    · rw [← add_assoc]
      exact (hsT _).symm
  refine ⟨k, c, hcF, hcyc, und (c 0), ?_⟩
  have hother : ∀ idx : Fin (k+1), idx ≠ 0 → und (c idx) ≠ und (c 0) := by
    intro idx hidx hund
    have hidx0 : 0 < (idx : ℕ) := by
      rcases Nat.eq_zero_or_pos (idx : ℕ) with h | h
      · exact absurd (Fin.ext h) hidx
      · exact h
    have hidxk : (idx : ℕ) ≤ k := Nat.lt_succ_iff.1 idx.isLt
    simp only [c, Fin.val_zero, add_zero] at hund
    set l := i + (idx : ℕ) with hl
    have hil : i < l := by omega
    have hlj : l < j := by omega
    -- endpoints of e_l are among the endpoints of e_i
    have hvl : vs l = vs i ∨ vs l = vs (i+1) := by
      have h1 := ends tail head (nx^[l] e0)
      have h2 := ends tail head (nx^[i] e0)
      have hT1 : vs (i+1) = aH tail head (nx^[i] e0) := hsT i
      simp only [hvs] at hT1 ⊢
      rw [hund] at h1
      rcases h1 with ⟨h1a, _⟩ | ⟨h1a, _⟩ <;> rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
      · left; rw [h1a, h2a]
      · right; rw [hT1, h1a, h2b]
      · right; rw [hT1, h1a, h2b]
      · left; rw [h1a, h2a]
    rcases hvl with hvl | hvl
    · exact hmin i l hil hlj hvl.symm
    · by_cases hi1 : i + 1 < j
      · have hl1 : l = i + 1 := by
          by_contra hne
          have : i + 1 < l := by omega
          exact hmin (i+1) l this hlj hvl.symm
        -- e_{i+1} = e_i
        have heq1 : nx^[i+1] e0 = nx^[i] e0 := by
          apply eq_of_und_eq
          · rw [← hl1]; exact hund
          · exact hsR i
        have hv2 : vs (i+2) = vs (i+1) := by
          simp only [hvs]
          have := hsT (i+1)
          rw [heq1] at this
          rw [this]
          exact (hsT i).symm
        by_cases hi2 : i + 2 < j
        · exact hmin (i+1) (i+2) (by omega) hi2 hv2.symm
        · have hj2 : j = i + 2 := by omega
          have : vs (i+1) = vs i := by rw [← hv2, ← hj2, ← heq]
          exact hmin i (i+1) (by omega) hi1 this.symm
      · omega
  have hsum : chiC c (und (c 0)) = evA (c 0) (und (c 0)) := by
    unfold chiC
    rw [Finset.sum_eq_single 0]
    · intro idx _ hidx
      by_contra h
      exact hother idx hidx (evA_ne_zero h)
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum]
  exact evA_und _

def isInt (t : ℝ) : Prop := ∃ n : ℤ, t = n

lemma isInt_sum (S : Finset A) (g : A → ℝ) (h : ∀ a ∈ S, isInt (g a)) :
    isInt (∑ a ∈ S, g a) := by
  refine Finset.sum_induction g isInt (fun a b ⟨m, hm⟩ ⟨n, hn⟩ => ⟨m + n, by rw [hm, hn]; push_cast; ring⟩)
    ⟨0, by simp⟩ h

lemma deg_cond (tail head : A → V) (xi : A → ℝ) (x : V → ℝ) (hb : Boundary tail head xi = x)
    (hx : ∀ v, isInt (x v)) (e : A ⊕ A) (he : ¬ isInt (xi (und e))) :
    ∃ e', ¬ isInt (xi (und e')) ∧ aT tail head e' = aH tail head e ∧ e' ≠ rev e := by
  by_contra hcon
  push_neg at hcon
  have hbv : Boundary tail head xi (aH tail head e) = x (aH tail head e) := congrFun hb _
  simp only [Boundary] at hbv
  obtain ⟨n, hn⟩ := hx (aH tail head e)
  cases e with
  | inl b =>
    have h1 : isInt (∑ a ∈ Finset.univ.filter (fun a => tail a = aH tail head (Sum.inl b)), xi a) := by
      apply isInt_sum; intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      by_contra hni
      have := hcon (.inl a) hni ha
      simp [rev] at this
    have h2 : isInt (∑ a ∈ (Finset.univ.filter (fun a => head a = aH tail head (Sum.inl b))).erase b,
        xi a) := by
      apply isInt_sum; intro a ha
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      by_contra hni
      have := hcon (.inr a) hni ha.2
      simp [rev] at this
      exact ha.1 this
    have hbmem : b ∈ Finset.univ.filter (fun a => head a = aH tail head (Sum.inl b)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
    rw [← Finset.add_sum_erase _ _ hbmem] at hbv
    obtain ⟨m1, hm1⟩ := h1; obtain ⟨m2, hm2⟩ := h2
    apply he; refine ⟨m1 - m2 - n, ?_⟩
    simp only [und]; push_cast; linarith
  | inr b =>
    have h1 : isInt (∑ a ∈ Finset.univ.filter (fun a => head a = aH tail head (Sum.inr b)), xi a) := by
      apply isInt_sum; intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      by_contra hni
      have := hcon (.inr a) hni ha
      simp [rev] at this
    have h2 : isInt (∑ a ∈ (Finset.univ.filter (fun a => tail a = aH tail head (Sum.inr b))).erase b,
        xi a) := by
      apply isInt_sum; intro a ha
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      by_contra hni
      have := hcon (.inl a) hni ha.2
      simp [rev] at this
      exact ha.1 this
    have hbmem : b ∈ Finset.univ.filter (fun a => tail a = aH tail head (Sum.inr b)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
    rw [← Finset.add_sum_erase _ _ hbmem] at hbv
    obtain ⟨m1, hm1⟩ := h1; obtain ⟨m2, hm2⟩ := h2
    apply he; refine ⟨n + m1 - m2, ?_⟩
    simp only [und]; push_cast; linarith

lemma fract_pos_of_not_int (t : ℝ) (h : ¬ isInt t) : 0 < Int.fract t := by
  rcases eq_or_lt_of_le (Int.fract_nonneg t) with h0 | h0
  · exact absurd (int_of_fract_eq_zero t h0.symm) h
  · exact h0

/-- The maximal step along a direction `y` keeping every moved coordinate within its unit box. -/
lemma step_box (xi y : A → ℝ) (hne : ∃ b, y b ≠ 0) (hni : ∀ b, y b ≠ 0 → ¬ isInt (xi b)) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ b, y b ≠ 0 → ((⌊xi b⌋ : ℤ) : ℝ) ≤ xi b + ε * y b ∧ xi b + ε * y b ≤ ⌊xi b⌋ + 1) ∧
      (∃ b, y b ≠ 0 ∧ isInt (xi b + ε * y b)) := by
  set t : A → ℝ := fun b => if 0 < y b then 1 - Int.fract (xi b) else Int.fract (xi b) with ht
  set r : A → ℝ := fun b => t b / |y b| with hr
  obtain ⟨b1, hb1T, hb1min⟩ := Finset.exists_min_image (Finset.univ.filter (fun b => y b ≠ 0)) r
    (by obtain ⟨b, hb⟩ := hne; exact ⟨b, by simp [hb]⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb1T hb1min
  have htpos : ∀ b, y b ≠ 0 → 0 < t b := by
    intro b hb
    have h1 := fract_pos_of_not_int _ (hni b hb)
    have h2 := Int.fract_lt_one (xi b)
    simp only [ht]; split_ifs <;> linarith
  have hεpos : 0 < r b1 := div_pos (htpos b1 hb1T) (abs_pos.2 hb1T)
  refine ⟨r b1, hεpos, fun b hb => ?_, b1, hb1T, ?_⟩
  · have hle : r b1 ≤ r b := hb1min b hb
    have hfl := Int.floor_add_fract (xi b)
    have hf1 := Int.fract_lt_one (xi b)
    have hf0 := Int.fract_nonneg (xi b)
    rcases lt_or_gt_of_ne hb with hneg | hpos
    · have habs : |y b| = -y b := abs_of_neg hneg
      have htb : t b = Int.fract (xi b) := by simp only [ht]; rw [if_neg (by linarith)]
      have : r b * y b = - Int.fract (xi b) := by
        simp only [hr, habs, htb]; field_simp
      have h3 : r b1 * y b ≥ r b * y b := by nlinarith
      constructor <;> nlinarith [hεpos]
    · have habs : |y b| = y b := abs_of_pos hpos
      have htb : t b = 1 - Int.fract (xi b) := by simp only [ht]; rw [if_pos hpos]
      have : r b * y b = 1 - Int.fract (xi b) := by
        simp only [hr, habs, htb]; field_simp
      have h3 : r b1 * y b ≤ r b * y b := by nlinarith
      constructor <;> nlinarith [hεpos]
  · have hfl := Int.floor_add_fract (xi b1)
    rcases lt_or_gt_of_ne hb1T with hneg | hpos
    · have habs : |y b1| = -y b1 := abs_of_neg hneg
      have htb : t b1 = Int.fract (xi b1) := by simp only [ht]; rw [if_neg (by linarith)]
      have : r b1 * y b1 = - Int.fract (xi b1) := by
        simp only [hr, habs, htb]; field_simp
      refine ⟨⌊xi b1⌋, ?_⟩
      linarith
    · have habs : |y b1| = y b1 := abs_of_pos hpos
      have htb : t b1 = 1 - Int.fract (xi b1) := by simp only [ht]; rw [if_pos hpos]
      have : r b1 * y b1 = 1 - Int.fract (xi b1) := by
        simp only [hr, habs, htb]; field_simp
      refine ⟨⌊xi b1⌋ + 1, ?_⟩
      push_cast; linarith

lemma push_feas (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ)
    (hcU : ∀ a, cUpper a = ⊤ ∨ ∃ n : ℤ, cUpper a = ((n:ℝ) : WithTop ℝ))
    (hcL : ∀ a, cLower a = ⊥ ∨ ∃ n : ℤ, cLower a = ((n:ℝ) : WithBot ℝ))
    (xi : A → ℝ)
    (hfe : FeasibleFlowMCFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi)
    (xi' : A → ℝ)
    (h : ∀ b, xi' b = xi b ∨ (¬ isInt (xi b) ∧ ((⌊xi b⌋ : ℤ) : ℝ) ≤ xi' b ∧ xi' b ≤ ⌊xi b⌋ + 1))
    (hb : Boundary tail head xi' = x) :
    FeasibleFlowMCFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x) xi' := by
  rw [feas0_iff'] at hfe ⊢
  refine ⟨fun a => ?_, hb⟩
  rcases h a with heq | ⟨hni, hlo, hhi⟩
  · rw [heq]; exact hfe.1 a
  · have hfa := hfe.1 a
    constructor
    · rcases hcL a with h0 | ⟨n, hn⟩
      · rw [h0]; exact bot_le
      · rw [hn] at hfa ⊢
        have h1 : (n : ℝ) ≤ xi a := WithBot.coe_le_coe.1 hfa.1
        have h2 : n ≤ ⌊xi a⌋ := Int.le_floor.2 h1
        have h3 : (n : ℝ) ≤ ⌊xi a⌋ := by exact_mod_cast h2
        exact WithBot.coe_le_coe.2 (by linarith)
    · rcases hcU a with h0 | ⟨n, hn⟩
      · rw [h0]; exact le_top
      · rw [hn] at hfa ⊢
        have h1 : xi a ≤ n := WithTop.coe_le_coe.1 hfa.2
        have h1' : xi a < n := lt_of_le_of_ne h1 (fun h => hni ⟨n, h⟩)
        have h2 : ⌊xi a⌋ < n := Int.floor_lt.2 h1'
        have h3 : ⌊xi a⌋ + 1 ≤ n := h2
        have h4 : ((⌊xi a⌋ : ℤ) : ℝ) + 1 ≤ n := by exact_mod_cast h3
        exact WithTop.coe_le_coe.2 (by linarith)

lemma cost_shift (gamma xi y : A → ℝ) (ε : ℝ) :
    ∑ a, gamma a * (xi a + ε * y a) = ∑ a, gamma a * xi a + ε * ∑ a, gamma a * y a := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => by ring)

lemma reduce_frac (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ)
    (hcU : ∀ a, cUpper a = ⊤ ∨ ∃ n : ℤ, cUpper a = ((n:ℝ) : WithTop ℝ))
    (hcL : ∀ a, cLower a = ⊥ ∨ ∃ n : ℤ, cLower a = ((n:ℝ) : WithBot ℝ))
    (hx : ∀ v, ∃ n : ℤ, x v = (n:ℝ))
    (xi : A → ℝ) (hopt : OptimalFlowMCFP0 tail head cUpper cLower gamma x xi)
    (hF : (Finset.univ.filter (fun a => ¬ isInt (xi a))).Nonempty) :
    ∃ xi', OptimalFlowMCFP0 tail head cUpper cLower gamma x xi' ∧
      (Finset.univ.filter (fun a => ¬ isInt (xi' a))).card <
        (Finset.univ.filter (fun a => ¬ isInt (xi a))).card := by
  unfold OptimalFlowMCFP0 at hopt ⊢
  unfold OptimalFlowMCFP3 at hopt ⊢
  have hfe := hopt.1
  have hfe' := (feas0_iff' tail head cUpper cLower gamma x xi).1 hfe
  have hdeg : ∀ e : A ⊕ A, und e ∈ Finset.univ.filter (fun a => ¬ isInt (xi a)) →
      ∃ e', und e' ∈ Finset.univ.filter (fun a => ¬ isInt (xi a)) ∧
        aT tail head e' = aH tail head e ∧ e' ≠ rev e := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨e', h1, h2, h3⟩ := deg_cond tail head xi x hfe'.2 hx e he
    exact ⟨e', by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h1, h2, h3⟩
  obtain ⟨k, c, hcF, hcyc, b0, hb0⟩ := walk_cycle tail head _ hF hdeg
  set χ := chiC c with hχ
  have hχF : ∀ b, χ b ≠ 0 → ¬ isInt (xi b) := by
    intro b hb
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    have := hcF i
    rw [evA_ne_zero hi] at this
    simpa using this
  have hχbd := boundary_chi tail head c hcyc
  -- the two pushes
  obtain ⟨εp, hεp, hboxp, bp, hbp, hbpint⟩ := step_box xi χ ⟨b0, hb0⟩ hχF
  obtain ⟨εm, hεm, hboxm, _⟩ := step_box xi (fun b => -χ b) ⟨b0, by simpa using hb0⟩
    (fun b hb => hχF b (by simpa using hb))
  set xip : A → ℝ := fun b => xi b + εp * χ b with hxip
  set xim : A → ℝ := fun b => xi b + εm * (-χ b) with hxim
  have hfp : FeasibleFlowMCFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x)
      xip := by
    apply push_feas tail head cUpper cLower gamma x hcU hcL xi hfe xip
    · intro b
      by_cases hb : χ b = 0
      · left; simp [hxip, hb]
      · right; exact ⟨hχF b hb, hboxp b hb⟩
    · funext v
      simp only [hxip]
      rw [boundary_lin, hfe'.2, hχbd]; simp
  have hfm : FeasibleFlowMCFP3 tail head (ArcCostMCFP0 cUpper cLower gamma) (BoundaryCostMCFP0 x)
      xim := by
    apply push_feas tail head cUpper cLower gamma x hcU hcL xi hfe xim
    · intro b
      by_cases hb : χ b = 0
      · left; simp [hxim, hb]
      · right; exact ⟨hχF b hb, hboxm b (by simpa using hb)⟩
    · funext v
      simp only [hxim]
      have : (fun b => xi b + εm * -χ b) = fun b => xi b + (-εm) * χ b := by
        funext b; ring
      rw [this, boundary_lin, hfe'.2, hχbd]; simp
  -- the cost of the cycle vanishes
  set L := ∑ a, gamma a * χ a with hL
  have hcp := hopt.2 xip hfp
  have hcm := hopt.2 xim hfm
  rw [gam0' tail head cUpper cLower gamma x xi hfe, gam0' tail head cUpper cLower gamma x xip hfp,
    WithTop.coe_le_coe] at hcp
  rw [gam0' tail head cUpper cLower gamma x xi hfe, gam0' tail head cUpper cLower gamma x xim hfm,
    WithTop.coe_le_coe] at hcm
  simp only [hxip] at hcp
  simp only [hxim] at hcm
  rw [cost_shift] at hcp
  have hcm' : ∑ a, gamma a * (xi a + εm * -χ a) = ∑ a, gamma a * xi a + (-εm) * L := by
    rw [← cost_shift]; exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [hcm'] at hcm
  have hL0 : L = 0 := by
    have h1 : 0 ≤ εp * L := by linarith
    have h2 : 0 ≤ -εm * L := by linarith
    rcases lt_trichotomy L 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  refine ⟨xip, ⟨hfp, fun xi'' h'' => ?_⟩, ?_⟩
  · have := hopt.2 xi'' h''
    rw [gam0' tail head cUpper cLower gamma x xi hfe] at this
    rw [gam0' tail head cUpper cLower gamma x xip hfp]
    simp only [hxip]
    rw [cost_shift, ← hL, hL0, mul_zero, add_zero]
    exact this
  · apply Finset.card_lt_card
    refine ⟨fun b hb => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      by_cases hχb : χ b = 0
      · simp only [hxip, hχb, mul_zero, add_zero] at hb; exact hb
      · exact hχF b hχb
    · have hbpF : bp ∈ Finset.univ.filter (fun a => ¬ isInt (xi a)) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hχF bp hbp
      have := hsub hbpF
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this hbpint

theorem primal_part (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (hopt : ∃ xi, OptimalFlowMCFP0 tail head cUpper cLower gamma x xi)
    (hcU : ∀ a, cUpper a = ⊤ ∨ ∃ n : ℤ, cUpper a = ((n:ℝ) : WithTop ℝ))
    (hcL : ∀ a, cLower a = ⊥ ∨ ∃ n : ℤ, cLower a = ((n:ℝ) : WithBot ℝ))
    (hx : ∀ v, ∃ n : ℤ, x v = (n:ℝ)) :
    ∃ xiZ : A → ℤ, OptimalFlowMCFP0 tail head cUpper cLower gamma x (fun a => (xiZ a : ℝ)) := by
  suffices h : ∀ n : ℕ, ∀ xi, OptimalFlowMCFP0 tail head cUpper cLower gamma x xi →
      (Finset.univ.filter (fun a => ¬ isInt (xi a))).card = n →
      ∃ xiZ : A → ℤ, OptimalFlowMCFP0 tail head cUpper cLower gamma x (fun a => (xiZ a : ℝ)) by
    obtain ⟨xi, hxi⟩ := hopt
    exact h _ xi hxi rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro xi hxi hn
  by_cases hF : (Finset.univ.filter (fun a => ¬ isInt (xi a))).Nonempty
  · obtain ⟨xi', hxi', hlt⟩ := reduce_frac tail head cUpper cLower gamma x hcU hcL hx xi hxi hF
    rw [hn] at hlt
    exact ih _ hlt xi' hxi' rfl
  · have hall : ∀ a, isInt (xi a) := by
      intro a; by_contra h
      exact hF ⟨a, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h⟩
    choose xiZ hxiZ using hall
    refine ⟨xiZ, ?_⟩
    have : (fun a => (xiZ a : ℝ)) = xi := by funext a; exact (hxiZ a).symm
    rw [this]; exact hxi

theorem mcfp0_integrality_core (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (hopt : ∃ xi, OptimalFlowMCFP0 tail head cUpper cLower gamma x xi) :
    ((∀ a, cUpper a = ⊤ ∨ ∃ n : ℤ, cUpper a = ((n:ℝ) : WithTop ℝ)) ∧
      (∀ a, cLower a = ⊥ ∨ ∃ n : ℤ, cLower a = ((n:ℝ) : WithBot ℝ)) ∧
      (∀ v, ∃ n : ℤ, x v = (n:ℝ)) →
        ∃ xiZ : A → ℤ, OptimalFlowMCFP0 tail head cUpper cLower gamma x (fun a => (xiZ a : ℝ))) ∧
    LConvexPolyhedronR (OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) ∧
    ((∀ a, ∃ n : ℤ, gamma a = (n:ℝ)) →
      IsIntegralPolyhedron (OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) ∧
      ∃ pZ : V → ℤ, (fun v => (pZ v : ℝ)) ∈ OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) := by
  obtain ⟨hL, hD⟩ := dual_part tail head cUpper cLower gamma x hopt
  exact ⟨fun ⟨h1, h2, h3⟩ => primal_part tail head cUpper cLower gamma x hopt h1 h2 h3, hL, hD⟩

end Primal

end DiscreteConvex.NetworkFlowsB

open DiscreteConvex.NetworkFlowsB
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem solution (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (x : V → ℝ) (hopt : ∃ xi, OptimalFlowMCFP0 tail head cUpper cLower gamma x xi) :
    ((∀ a, cUpper a = ⊤ ∨ ∃ n : ℤ, cUpper a = ((n:ℝ) : WithTop ℝ)) ∧
      (∀ a, cLower a = ⊥ ∨ ∃ n : ℤ, cLower a = ((n:ℝ) : WithBot ℝ)) ∧
      (∀ v, ∃ n : ℤ, x v = (n:ℝ)) →
        ∃ xiZ : A → ℤ, OptimalFlowMCFP0 tail head cUpper cLower gamma x (fun a => (xiZ a : ℝ))) ∧
    LConvexPolyhedronR (OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) ∧
    ((∀ a, ∃ n : ℤ, gamma a = (n:ℝ)) →
      IsIntegralPolyhedron (OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) ∧
      ∃ pZ : V → ℤ, (fun v => (pZ v : ℝ)) ∈ OptimalPotentialSetMCFP0 tail head cUpper cLower gamma x) := by
  exact mcfp0_integrality_core tail head cUpper cLower gamma x hopt
