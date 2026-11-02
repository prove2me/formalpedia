-- Prove2me | solution 1 for DiscreteConvex.NetworkFlowsB.msfp3_polyhedral_structure
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:50:18.019159+00:00
-- url     : https://prove2.me/submissions/3204e3fb-e8d7-4f17-9052-980d673b70a6

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedralConvexArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_M2ConvexPolyhedronR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_LConvexPolyhedronR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDomainIntegerArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDomainIntegerR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDualIntegralArc
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsDualIntegralR
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryOptSetMSFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetMSFP3
import Theorems.Thm_DiscreteConvex_NetworkFlowsB_potential_criterion_msfp3

open Classical
open scoped Pointwise BigOperators

namespace DiscreteConvex.NetworkFlowsB

/-! ## Section 1: Difference-constraint polyhedra (L-convexity and integrality) -/

section DiffSetSec
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

def DiffSet {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ) : Set (V → ℝ) :=
  {p | ∀ i, Q i → p (u i) - p (v i) ≤ c i}

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
    (hc : ∀ i, Q i → ∃ n : ℤ, c i = n) {p : V → ℝ} (hp : p ∈ DiffSet Q u v c) :
    (fun w => ((⌊p w⌋ : ℤ) : ℝ)) ∈ DiffSet Q u v c := by
  intro i hi
  obtain ⟨n, hn⟩ := hc i hi
  have := hp i hi
  rw [hn] at this ⊢
  exact floor_diff_le this

lemma diffSet_ceil {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ)
    (hc : ∀ i, Q i → ∃ n : ℤ, c i = n) {p : V → ℝ} (hp : p ∈ DiffSet Q u v c) :
    (fun w => ((⌈p w⌉ : ℤ) : ℝ)) ∈ DiffSet Q u v c := by
  intro i hi
  obtain ⟨n, hn⟩ := hc i hi
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

lemma diffSet_hull {ι : Type*} (Q : ι → Prop) (u v : ι → V) (c : ι → ℝ)
    (hc : ∀ i, Q i → ∃ n : ℤ, c i = n) :
    ∀ n : ℕ, ∀ p ∈ DiffSet Q u v c,
      (Finset.univ.filter (fun w => Int.fract (p w) ≠ 0)).card = n →
      p ∈ convexHull ℝ (DiffSet Q u v c ∩ ZPts) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hp hn
  by_cases hF : (Finset.univ.filter (fun w => Int.fract (p w) ≠ 0)) = ∅
  · apply subset_convexHull
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
    set q : V → ℝ := fun w => ((⌈p w⌉ : ℤ) : ℝ) with hq
    have hqS : q ∈ DiffSet Q u v c := diffSet_ceil Q u v c hc hp
    have hqZ : q ∈ ZPts := fun w => ⟨⌈p w⌉, rfl⟩
    set p' : V → ℝ := fun w => (p w - θ * q w) / (1 - θ) with hp'
    have h1θ : 0 < 1 - θ := by linarith
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
      obtain ⟨m, hm⟩ := hc i hi
      have h1 := hp i hi
      have h2 := hqS i hi
      simp only [hp']
      rw [div_sub_div_same, div_le_iff₀ h1θ]
      rw [hm] at h1 h2 ⊢
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
    (hc : ∀ i, Q i → ∃ n : ℤ, c i = n) :
    IsIntegralPolyhedron (DiffSet Q u v c) := by
  unfold IsIntegralPolyhedron
  apply le_antisymm
  · intro p hp
    exact diffSet_hull Q u v c hc _ p hp rfl
  · exact convexHull_min Set.inter_subset_left (diffSet_convex Q u v c)

end DiffSetSec

/-! ## Section 2: Fourier–Motzkin projection of polyhedra -/

section FMElim
set_option linter.unusedSectionVars false

lemma interval_feasible {I J : Type*} [Fintype I] [Fintype J]
    (l : I → ℝ) (u : J → ℝ) (h : ∀ i j, l i ≤ u j) :
    ∃ t : ℝ, (∀ i, l i ≤ t) ∧ (∀ j, t ≤ u j) := by
  cases isEmpty_or_nonempty I with
  | inl hI =>
    letI := hI
    cases isEmpty_or_nonempty J with
    | inl hJ =>
      letI := hJ
      exact ⟨0, fun i => isEmptyElim i, fun j => isEmptyElim j⟩
    | inr hJ =>
      letI := hJ
      refine ⟨Finset.univ.inf' Finset.univ_nonempty u, fun i => isEmptyElim i, ?_⟩
      intro j
      exact Finset.inf'_le u (Finset.mem_univ j)
  | inr hI =>
    letI := hI
    refine ⟨Finset.univ.sup' Finset.univ_nonempty l, ?_, ?_⟩
    · intro i; exact Finset.le_sup' l (Finset.mem_univ i)
    · intro j; exact Finset.sup'_le Finset.univ_nonempty l (fun i _ => h i j)

abbrev ElimRows {I : Type*} (a : I → ℝ) := {i : I // a i = 0} ⊕
  ({i : I // 0 < a i} × {i : I // a i < 0})

noncomputable def rowWeights {I : Type*} [DecidableEq I] (a : I → ℝ) : ElimRows a → I → ℝ
  | .inl i, k => if k = i.1 then 1 else 0
  | .inr ij, k => (if k = ij.1.1 then (a ij.1.1)⁻¹ else 0) +
      (if k = ij.2.1 then -(a ij.2.1)⁻¹ else 0)

lemma rowWeights_nonneg {I : Type*} [DecidableEq I] (a : I → ℝ)
    (j : ElimRows a) (i : I) : 0 ≤ rowWeights a j i := by
  cases j with
  | inl j => simp only [rowWeights]; split <;> norm_num
  | inr j =>
    apply add_nonneg
    · split <;> simp_all [le_of_lt j.1.2]
    · split <;> simp_all [le_of_lt j.2.2]

lemma rowWeights_sum {I : Type*} [Fintype I] [DecidableEq I] (a f : I → ℝ)
    (j : ElimRows a) : (∑ i, rowWeights a j i * f i) =
    match j with
    | .inl k => f k.1
    | .inr kl => f kl.1.1 / a kl.1.1 - f kl.2.1 / a kl.2.1 := by
  cases j with
  | inl j => simp [rowWeights]
  | inr j =>
    simp only [rowWeights, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp [div_eq_mul_inv, mul_comm, sub_eq_add_neg]

lemma rowWeights_annihilate {I : Type*} [Fintype I] [DecidableEq I] (a : I → ℝ)
    (j : ElimRows a) : ∑ i, rowWeights a j i * a i = 0 := by
  rw [rowWeights_sum]
  cases j with
  | inl j => exact j.2
  | inr j => simp [ne_of_gt j.1.2, ne_of_lt j.2.2]

lemma elim_one_iff {I : Type*} [Fintype I] [DecidableEq I] (a0 R : I → ℝ) :
    (∃ t : ℝ, ∀ i : I, R i ≤ a0 i * t) ↔
      (∀ j : ElimRows a0, ∑ i : I, rowWeights a0 j i * R i ≤ 0) := by
  constructor
  · rintro ⟨t, ht⟩ j
    have hle : ∑ i : I, rowWeights a0 j i * R i ≤ ∑ i : I, rowWeights a0 j i * (a0 i * t) := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact mul_le_mul_of_nonneg_left (ht i) (rowWeights_nonneg a0 j i)
    have h0 : ∑ i : I, rowWeights a0 j i * (a0 i * t) = (∑ i : I, rowWeights a0 j i * a0 i) * t := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h0, rowWeights_annihilate, zero_mul] at hle
    exact hle
  · intro hR
    have hpair (p : {i : I // 0 < a0 i}) (q : {i : I // a0 i < 0}) :
        R p.1 / a0 p.1 ≤ R q.1 / a0 q.1 := by
      have hh := hR (Sum.inr (p, q))
      rw [rowWeights_sum] at hh
      exact sub_nonpos.mp hh
    obtain ⟨t, htp, htn⟩ := interval_feasible
      (fun p : {i : I // 0 < a0 i} => R p.1 / a0 p.1)
      (fun q : {i : I // a0 i < 0} => R q.1 / a0 q.1) hpair
    refine ⟨t, fun i => ?_⟩
    rcases lt_trichotomy (a0 i) 0 with hn | hz | hp
    · have hh := (le_div_iff_of_neg hn).mp (htn ⟨i, hn⟩)
      simpa only [mul_comm] using hh
    · have hh := hR (Sum.inl ⟨i, hz⟩)
      rw [rowWeights_sum] at hh
      simpa only [hz, zero_mul] using hh
    · have hh := (div_le_iff₀ hp).mp (htp ⟨i, hp⟩)
      simpa only [mul_comm] using hh

lemma isPolyhedron_exists_fin {V : Type*} [Fintype V] :
    ∀ (n : ℕ) {I : Type*} [Fintype I] [DecidableEq I]
      (C : I → V → ℝ) (D : I → Fin n → ℝ) (E : I → ℝ),
      IsPolyhedron {x : V → ℝ | ∃ z : Fin n → ℝ,
        ∀ i : I, ∑ v, C i v * x v + ∑ k : Fin n, D i k * z k ≤ E i} := by
  intro n
  induction n with
  | zero =>
    intro I _ _ C D E
    have h := isPolyhedron_of_fintype C E
    convert h using 1
    ext x
    simp only [Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨Fin.elim0, hx⟩⟩
  | succ n ih =>
    intro I _ _ C D E
    let a0 : I → ℝ := fun i => - D i 0
    let J := ElimRows a0
    let C' : J → V → ℝ := fun j v => ∑ i : I, rowWeights a0 j i * C i v
    let D' : J → Fin n → ℝ := fun j k => ∑ i : I, rowWeights a0 j i * D i k.succ
    let E' : J → ℝ := fun j => ∑ i : I, rowWeights a0 j i * E i
    have hJ := ih C' D' E'
    convert hJ using 1
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨fun k => z k.succ, ?_⟩
      have hex : ∃ t : ℝ, ∀ i : I,
          (∑ v, C i v * x v + ∑ k : Fin n, D i k.succ * z k.succ - E i) ≤ a0 i * t := by
        refine ⟨z 0, fun i => ?_⟩
        have hi := hz i
        rw [Fin.sum_univ_succ] at hi
        dsimp [a0]
        linarith
      rw [elim_one_iff] at hex
      intro j
      have hj := hex j
      have hlin : (∑ i : I, rowWeights a0 j i *
          (∑ v, C i v * x v + ∑ k : Fin n, D i k.succ * z k.succ - E i)) =
          (∑ v, C' j v * x v + ∑ k : Fin n, D' j k * z k.succ) - E' j := by
        dsimp [C', D', E']
        simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_mul, Finset.mul_sum]
        congr 1
        congr 1
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => by ring
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
      linarith
    · rintro ⟨z', hz'⟩
      have hex : ∀ j : J, ∑ i : I, rowWeights a0 j i *
          (∑ v, C i v * x v + ∑ k : Fin n, D i k.succ * z' k - E i) ≤ 0 := by
        intro j
        have hj := hz' j
        have hlin : (∑ i : I, rowWeights a0 j i *
            (∑ v, C i v * x v + ∑ k : Fin n, D i k.succ * z' k - E i)) =
            (∑ v, C' j v * x v + ∑ k : Fin n, D' j k * z' k) - E' j := by
          dsimp [C', D', E']
          simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.sum_mul, Finset.mul_sum]
          congr 1
          congr 1
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => by ring
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
        linarith
      rw [← elim_one_iff] at hex
      obtain ⟨t, ht⟩ := hex
      refine ⟨Fin.cons t z', fun i => ?_⟩
      have hi := ht i
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      dsimp [a0] at hi
      linarith

lemma isPolyhedron_exists_fintype {V A I : Type*} [Fintype V] [Fintype A] [Fintype I]
    [DecidableEq I] (C : I → V → ℝ) (D : I → A → ℝ) (E : I → ℝ) :
    IsPolyhedron {x : V → ℝ | ∃ xi : A → ℝ,
      ∀ i : I, ∑ v, C i v * x v + ∑ a : A, D i a * xi a ≤ E i} := by
  let e := Fintype.equivFin A
  have h := isPolyhedron_exists_fin (Fintype.card A) C (fun i k => D i (e.symm k)) E
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨xi, hxi⟩
    refine ⟨fun k => xi (e.symm k), fun i => ?_⟩
    have heq : (∑ k : Fin (Fintype.card A), D i (e.symm k) * xi (e.symm k)) =
        ∑ a : A, D i a * xi a := e.symm.sum_comp (fun a => D i a * xi a)
    rw [heq]
    exact hxi i
  · rintro ⟨z, hz⟩
    refine ⟨fun a => z (e a), fun i => ?_⟩
    have heq : (∑ a : A, D i a * z (e a)) =
        ∑ k : Fin (Fintype.card A), D i (e.symm k) * z k := by
      refine (e.symm.sum_comp (fun a => D i a * z (e a))).symm.trans ?_
      exact Finset.sum_congr rfl fun k _ => by simp
    rw [heq]
    exact hz i

end FMElim

/-! ## Section 3: Polyhedral ray slopes and global optimality for M-convex functions -/

section PolyhedralRay
set_option linter.unusedSectionVars false

lemma finite_positive_bound {I : Type*} [DecidableEq I] (s : Finset I)
    (f : I → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i ∈ s, e ≤ f i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨e, he, hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min e (f i), lt_min he (hf i (Finset.mem_insert_self _ _)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hbound j hj)

/-- Every polyhedral convex ray `φ : ℝ → WithTop ℝ` with `φ 0 = r0` and `∃ t1 > 0, φ t1 ≠ ⊤`
has a right-hand slope `c : ℝ` that is exact on `[0, ε]` for some `ε > 0` and lower-bounds `φ`
on `[0, ∞)`. -/
theorem polyhedral_ray_slope (φ : ℝ → WithTop ℝ) (r0 : ℝ) (m : ℕ) (α β γ : Fin m → ℝ)
    (h0 : φ 0 = (r0 : WithTop ℝ))
    (hrep : ∀ t r : ℝ, φ t ≤ (r : WithTop ℝ) ↔ ∀ i : Fin m, α i * t + β i * r ≤ γ i)
    (ht1 : ∃ t1 : ℝ, 0 < t1 ∧ φ t1 ≠ ⊤) :
    ∃ (c ε : ℝ), 0 < ε ∧
      (∀ t : ℝ, 0 ≤ t → ((r0 + c * t : ℝ) : WithTop ℝ) ≤ φ t) ∧
      (∀ δ : ℝ, 0 ≤ δ → δ ≤ ε → φ δ = ((r0 + c * δ : ℝ) : WithTop ℝ)) ∧
      (∀ s : ℝ, (∀ t : ℝ, 0 ≤ t → (r0 : WithTop ℝ) ≤ φ t + ((- s * t : ℝ) : WithTop ℝ)) ↔ s ≤ c) := by
  obtain ⟨t1, ht1_pos, ht1_ne⟩ := ht1
  obtain ⟨r1, hr1⟩ := WithTop.ne_top_iff_exists.mp ht1_ne
  have hrow0 : ∀ i : Fin m, β i * r0 ≤ γ i := by
    have := (hrep 0 r0).mp h0.le
    simpa using this
  have hrow1 : ∀ i : Fin m, α i * t1 + β i * r1 ≤ γ i :=
    (hrep t1 r1).mp hr1.symm.le
  have hβ : ∀ i : Fin m, β i ≤ 0 := by
    intro i
    by_contra hpos
    push_neg at hpos
    let r : ℝ := max r0 ((γ i + 1) / β i)
    have hr0_le : (φ 0) ≤ (r : WithTop ℝ) := by
      rw [h0, WithTop.coe_le_coe]
      exact le_max_left _ _
    have hi := (hrep 0 r).mp hr0_le i
    simp only [ mul_zero, zero_add] at hi
    have hge : (γ i + 1) / β i ≤ r := le_max_right _ _
    have hgt : γ i + 1 ≤ r * β i := (div_le_iff₀ hpos).mp hge
    linarith
  have hactive : ∃ i : Fin m, β i < 0 ∧ β i * r0 = γ i := by
    by_contra h
    push_neg at h
    let bnd : Fin m → ℝ := fun i =>
      if β i < 0 then (γ i - β i * r0) / (- β i) else 1
    have hbnd : ∀ i : Fin m, 0 < bnd i := by
      intro i
      dsimp [bnd]
      split_ifs with hbi
      · exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hrow0 i) (h i hbi))) (neg_pos.mpr hbi)
      · norm_num
    obtain ⟨e, he, heB⟩ := finite_positive_bound Finset.univ bnd (fun i _ => hbnd i)
    have hlow : φ 0 ≤ ((r0 - e : ℝ) : WithTop ℝ) := by
      apply (hrep 0 (r0 - e)).mpr
      intro i
      simp only [mul_zero, zero_add]
      by_cases hbi : β i < 0
      · have hb := heB i (Finset.mem_univ i)
        simp only [bnd, if_pos hbi] at hb
        have hc := (le_div_iff₀ (neg_pos.mpr hbi)).mp hb
        nlinarith
      · have hbi0 : β i = 0 := le_antisymm (hβ i) (le_of_not_gt hbi)
        rw [hbi0, zero_mul]
        simpa [hbi0] using hrow0 i
    rw [h0, WithTop.coe_le_coe] at hlow
    linarith
  let Act : Finset (Fin m) := Finset.univ.filter (fun i => β i < 0 ∧ β i * r0 = γ i)
  have hAct : Act.Nonempty := by
    obtain ⟨i, hi1, hi2⟩ := hactive
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi1, hi2⟩⟩
  let c : ℝ := Act.sup' hAct (fun i => α i / (- β i))
  obtain ⟨i0, hi0Act, hi0_eq⟩ := Finset.exists_mem_eq_sup' hAct (fun i => α i / (- β i))
  have hc_def : c = α i0 / (- β i0) := hi0_eq
  have hi0 : β i0 < 0 ∧ β i0 * r0 = γ i0 := (Finset.mem_filter.mp hi0Act).2
  have hAct_le : ∀ i : Fin m, β i < 0 → β i * r0 = γ i → α i + β i * c ≤ 0 := by
    intro i h1 h2
    have hmem : i ∈ Act := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1, h2⟩
    have hle : α i / (- β i) ≤ c := Finset.le_sup' (fun j => α j / (- β j)) hmem
    have hmul := (div_le_iff₀ (neg_pos.mpr h1)).mp hle
    linarith
  let stepBnd : Fin m → ℝ := fun i =>
    if β i < 0 ∧ β i * r0 < γ i then (γ i - β i * r0) / (|α i + β i * c| + 1) else t1
  have hstepBnd : ∀ i : Fin m, 0 < stepBnd i := by
    intro i
    dsimp [stepBnd]
    split_ifs with h
    · exact div_pos (sub_pos.mpr h.2) (by positivity)
    · exact ht1_pos
  obtain ⟨e1, he1_pos, he1B⟩ := finite_positive_bound Finset.univ stepBnd (fun i _ => hstepBnd i)
  let ε : ℝ := min t1 e1
  have hε_pos : 0 < ε := lt_min ht1_pos he1_pos
  have hlower : ∀ t : ℝ, 0 ≤ t → ((r0 + c * t : ℝ) : WithTop ℝ) ≤ φ t := by
    intro t ht
    induction hφt : φ t using WithTop.recTopCoe with
    | top => exact le_top
    | coe r =>
      rw [WithTop.coe_le_coe]
      have hi0_row := (hrep t r).mp hφt.le i0
      have hd0 : 0 < - β i0 := neg_pos.mpr hi0.1
      have hα0 : α i0 = (- β i0) * c := by
        rw [hc_def, mul_div_cancel₀ _ (ne_of_gt hd0)]
      nlinarith [hi0.2]
  have hupper : ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε → φ δ ≤ ((r0 + c * δ : ℝ) : WithTop ℝ) := by
    intro δ hδ0 hδε
    apply (hrep δ (r0 + c * δ)).mpr
    intro i
    have hδ_t1 : δ ≤ t1 := hδε.trans (min_le_left _ _)
    have hδ_e1 : δ ≤ e1 := hδε.trans (min_le_right _ _)
    rcases lt_or_eq_of_le (hβ i) with hbi_neg | hbi_zero
    · rcases lt_or_eq_of_le (hrow0 i) with hstrict | htight
      · have hb := hδ_e1.trans (he1B i (Finset.mem_univ i))
        have hcond : β i < 0 ∧ β i * r0 < γ i := ⟨hbi_neg, hstrict⟩
        dsimp only [stepBnd] at hb
        rw [if_pos hcond] at hb
        have hm := (le_div_iff₀ (by positivity : 0 < |α i + β i * c| + 1)).mp hb
        have habs : α i + β i * c ≤ |α i + β i * c| := le_abs_self _
        nlinarith
      · have hle := hAct_le i hbi_neg htight
        nlinarith
    · have h0_γ : 0 ≤ γ i := by simpa [hbi_zero] using hrow0 i
      have h1_γ : α i * t1 ≤ γ i := by simpa [hbi_zero] using hrow1 i
      rw [hbi_zero, zero_mul, add_zero]
      rcases le_or_gt (α i) 0 with hα_neg | hα_pos
      · nlinarith
      · nlinarith
  have hexact : ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε → φ δ = ((r0 + c * δ : ℝ) : WithTop ℝ) := by
    intro δ hδ0 hδε
    exact le_antisymm (hupper δ hδ0 hδε) (hlower δ hδ0)
  refine ⟨c, ε, hε_pos, hlower, hexact, fun s => ?_⟩
  constructor
  · intro hs
    have hε_in := hs ε hε_pos.le
    rw [hexact ε hε_pos.le le_rfl, ← WithTop.coe_add, WithTop.coe_le_coe] at hε_in
    nlinarith
  · intro hsc t ht
    have hlow := hlower t ht
    induction hφt : φ t using WithTop.recTopCoe with
    | top => simp
    | coe r =>
      rw [hφt, WithTop.coe_le_coe] at hlow
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

def epiPoint (p : V → ℝ) (r : ℝ) : Option V → ℝ
  | none => r
  | some v => p v

@[simp] theorem row_epi (a : Option V → ℝ) (p : V → ℝ) (r : ℝ) :
    (∑ w, a w * epiPoint p r w) = a none * r + ∑ v, a (some v) * p v := by
  simp [Fintype.sum_option, epiPoint]

theorem closed_sublevel (f : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex f) (c : ℝ) : IsClosed {z | f z ≤ (c : WithTop ℝ)} := by
  obtain ⟨m, a, b, hab⟩ := hpoly
  have hset : {z | f z ≤ (c : WithTop ℝ)} =
      ⋂ i : Fin m, {z | a i none * c + ∑ v, a i (some v) * z v ≤ b i} := by
    ext z
    have h := Set.ext_iff.mp hab (epiPoint z c)
    simpa [epiPoint, Fintype.sum_option] using h
  rw [hset]
  apply isClosed_iInter
  intro i
  apply isClosed_le
  · fun_prop
  · fun_prop

theorem global_min_of_exchange_rays (f : (V → ℝ) → WithTop ℝ)
    (hclosed : ∀ c : ℝ, IsClosed {z | f z ≤ (c : WithTop ℝ)}) (hf : MExchangeAxiomR f)
    (x : V → ℝ) (hx : f x ≠ ⊤)
    (hray : ∀ u v : V, ∀ t : ℝ, 0 ≤ t →
      f x ≤ f (fun w => x w + t * ((if w = v then (1 : ℝ) else 0) - (if w = u then (1 : ℝ) else 0)))) :
    ∀ y, f x ≤ f y := by
  intro y
  by_contra hnot
  have hfy : f y < f x := lt_of_not_ge hnot
  have hy : f y ≠ ⊤ := ne_top_of_lt hfy
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hy
  let lo : V → ℝ := fun v => min (x v) (y v)
  let hi : V → ℝ := fun v => max (x v) (y v)
  let S := Set.Icc lo hi ∩ {z : V → ℝ | f z ≤ (c : WithTop ℝ)}
  have hSne : S.Nonempty := by
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · intro v; exact min_le_right _ _
    · intro v; exact le_max_right _ _
    · exact hc.symm.le
  have hSc : IsCompact S := isCompact_Icc.inter_right (hclosed c)
  have hcont : Continuous (fun z : V → ℝ => ∑ v, |z v - x v|) := by fun_prop
  obtain ⟨z, hz, hmin⟩ := hSc.exists_isMinOn hSne hcont.continuousOn
  have hzlow : f z ≤ f y := by simpa only [Set.mem_setOf_eq, hc] using hz.2
  have hzdom : f z ≠ ⊤ := ne_top_of_le_ne_top hy hzlow
  have hzne : z ≠ x := by
    intro heq
    rw [heq] at hzlow
    exact (not_le_of_gt hfy) hzlow
  have hex : ∃ u : V, x u < z u := by
    by_contra h
    push_neg at h
    have hcoord : ∃ u : V, z u < x u := by
      by_contra hh
      push_neg at hh
      apply hzne
      funext u
      exact le_antisymm (h u) (hh u)
    obtain ⟨u, hu⟩ := hcoord
    have hu' : u ∈ SuppPosR x z := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
    obtain ⟨v, hv, _⟩ := hf x hx z hzdom u hu'
    have hv' : x v < z v := (Finset.mem_filter.mp hv).2
    exact (not_lt_of_ge (h v)) hv'
  obtain ⟨u, hu⟩ := hex
  have hu' : u ∈ SuppPosR z x := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
  obtain ⟨v, hv, a0, ha0, hexc⟩ := hf z hzdom x hx u hu'
  have hv' : z v < x v := (Finset.mem_filter.mp hv).2
  have huv : u ≠ v := by intro heq; subst v; linarith
  let t : ℝ := min a0 (min (z u - x u) (x v - z v)) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hta : t ≤ a0 := by dsimp [t]; linarith [min_le_left a0 (min (z u - x u) (x v - z v))]
  have htu : t ≤ z u - x u := by
    have hh := (min_le_right a0 (min (z u - x u) (x v - z v))).trans (min_le_left _ _)
    dsimp [t]; linarith
  have htv : t ≤ x v - z v := by
    have hh := (min_le_right a0 (min (z u - x u) (x v - z v))).trans (min_le_right _ _)
    dsimp [t]; linarith
  let z' : V → ℝ := fun w => z w - t * (if w = u then (1:ℝ) else 0) + t * (if w = v then (1:ℝ) else 0)
  let x' : V → ℝ := fun w => x w + t * (if w = u then (1:ℝ) else 0) - t * (if w = v then (1:ℝ) else 0)
  have hxray : f x ≤ f x' := by
    have h1 := hray v u t ht.le
    convert h1 using 2
    funext w; ring
  have hznew : f z' ≤ f z := by
    have hh : f z' + f x ≤ f z + f x :=
      (add_le_add_right hxray (f z')).trans (hexc t ht.le hta)
    exact (WithTop.add_le_add_iff_right hx).mp hh
  have hz'box : z' ∈ Set.Icc lo hi := by
    constructor <;> intro w
    · by_cases hwu : w = u
      · subst w
        simp only [z', if_true, if_neg huv, mul_one, mul_zero, add_zero]
        exact (min_le_left _ _).trans (by linarith)
      · by_cases hwv : w = v
        · subst w
          simp only [z', if_true, if_neg (Ne.symm huv), mul_one, mul_zero, sub_zero]
          exact (hz.1.1 v).trans (by linarith)
        · simpa [z', hwu, hwv] using hz.1.1 w
    · by_cases hwu : w = u
      · subst w
        simp only [z', if_true, if_neg huv, mul_one, mul_zero, add_zero]
        exact (show z u - t ≤ z u by linarith).trans (hz.1.2 u)
      · by_cases hwv : w = v
        · subst w
          simp only [z', if_true, if_neg (Ne.symm huv), mul_one, mul_zero, sub_zero]
          exact (show z v + t ≤ x v by linarith).trans (le_max_left _ _)
        · simpa [z', hwu, hwv] using hz.1.2 w
  have hz'S : z' ∈ S := ⟨hz'box, hznew.trans hz.2⟩
  have hdiff : (∑ w, |z' w - x w|) = (∑ w, |z w - x w|) - 2 * t := by
    have hpoint (w : V) : |z' w - x w| = |z w - x w| -
        (if w = u then t else 0) - (if w = v then t else 0) := by
      by_cases hwu : w = u
      · subst w
        simp only [z', if_true, if_neg huv, mul_one, mul_zero, add_zero, sub_zero]
        rw [abs_of_nonneg (by linarith : 0 ≤ z u - t - x u), abs_of_pos (sub_pos.mpr hu)]
        ring
      · by_cases hwv : w = v
        · subst w
          simp only [z', if_true, if_neg (Ne.symm huv), mul_one, mul_zero, sub_zero]
          rw [abs_of_nonpos (by linarith : z v + t - x v ≤ 0), abs_of_neg (sub_neg.mpr hv')]
          ring
        · simp [z', hwu, hwv]
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
    ring
  have hbad : (∑ w, |z w - x w|) ≤ (∑ w, |z' w - x w|) := hmin hz'S
  rw [hdiff] at hbad
  linarith

end PolyhedralRay

/-! ## Section 4: Dual structure and integrality of `OptimalPotentialSetMSFP3` -/

section DualPart
set_option linter.unusedSectionVars false

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma mexc_reducedBoundary (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f) (p : V → ℝ) :
    MExchangeAxiomR (ReducedBoundaryCost f p) := by
  intro x hx y hy u hu
  have hx' : f x ≠ ⊤ := by
    intro h; apply hx; simp [ReducedBoundaryCost, h]
  have hy' : f y ≠ ⊤ := by
    intro h; apply hy; simp [ReducedBoundaryCost, h]
  obtain ⟨v, hv, α0, hα0, H⟩ := hf x hx' y hy' u hu
  refine ⟨v, hv, α0, hα0, fun α h0 h1 => ?_⟩
  have Hα := H α h0 h1
  set x' : V → ℝ := fun w => x w - α * (if w = u then (1:ℝ) else 0) + α * (if w = v then (1:ℝ) else 0)
  set y' : V → ℝ := fun w => y w + α * (if w = u then (1:ℝ) else 0) - α * (if w = v then (1:ℝ) else 0)
  have hsum : (∑ w, p w * x' w) + (∑ w, p w * y' w) = (∑ w, p w * x w) + (∑ w, p w * y w) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [x', y']; ring
  obtain ⟨rx, hrx⟩ := WithTop.ne_top_iff_exists.mp hx'
  obtain ⟨ry, hry⟩ := WithTop.ne_top_iff_exists.mp hy'
  have hx'' : f x' ≠ ⊤ := by
    intro h; rw [h, top_add] at Hα; rw [← hrx, ← hry, ← WithTop.coe_add] at Hα; exact WithTop.top_le_iff.mp Hα |> WithTop.coe_ne_top
  have hy'' : f y' ≠ ⊤ := by
    intro h; rw [h, add_top] at Hα; rw [← hrx, ← hry, ← WithTop.coe_add] at Hα; exact WithTop.top_le_iff.mp Hα |> WithTop.coe_ne_top
  obtain ⟨rx', hrx'⟩ := WithTop.ne_top_iff_exists.mp hx''
  obtain ⟨ry', hry'⟩ := WithTop.ne_top_iff_exists.mp hy''
  rw [← hrx, ← hry, ← hrx', ← hry', ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at Hα
  simp only [ReducedBoundaryCost, ← hrx, ← hry, ← hrx', ← hry']
  change (((rx - ∑ w, p w * x w : ℝ) : WithTop ℝ) + ((ry - ∑ w, p w * y w : ℝ) : WithTop ℝ) ≥
    ((rx' - ∑ w, p w * x' w : ℝ) : WithTop ℝ) + ((ry' - ∑ w, p w * y' w : ℝ) : WithTop ℝ))
  rw [ge_iff_le, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  linarith

lemma poly_reducedBoundary (f : (V → ℝ) → WithTop ℝ) (hfPoly : IsPolyhedralConvex f) (p : V → ℝ) :
    IsPolyhedralConvex (ReducedBoundaryCost f p) := by
  obtain ⟨m, a, b, hab⟩ := hfPoly
  refine ⟨m, fun i o => Option.elim o (a i none) (fun v => a i (some v) + a i none * p v), b, ?_⟩
  ext q
  simp only [Set.mem_setOf_eq, ReducedBoundaryCost]
  have h1 : f (fun v => q (some v)) - ((∑ v, p v * q (some v) : ℝ) : WithTop ℝ) ≤ ((q none : ℝ) : WithTop ℝ) ↔
      f (fun v => q (some v)) ≤ ((q none + ∑ v, p v * q (some v) : ℝ) : WithTop ℝ) := by
    let S : ℝ := ∑ v, p v * q (some v)
    change f (fun v => q (some v)) - (S : WithTop ℝ) ≤ ((q none : ℝ) : WithTop ℝ) ↔
      f (fun v => q (some v)) ≤ ((q none + S : ℝ) : WithTop ℝ)
    induction f (fun v => q (some v)) using WithTop.recTopCoe with
    | top =>
      change ⊤ ≤ ((q none : ℝ) : WithTop ℝ) ↔ ⊤ ≤ ((q none + S : ℝ) : WithTop ℝ)
      simp
    | coe r =>
      change ((r - S : ℝ) : WithTop ℝ) ≤ ((q none : ℝ) : WithTop ℝ) ↔ _
      rw [WithTop.coe_le_coe, WithTop.coe_le_coe]
      constructor <;> intro h <;> linarith
  rw [h1]
  have h2 := Set.ext_iff.mp hab (epiPoint (fun v => q (some v)) (q none + ∑ v, p v * q (some v)))
  simp only [Set.mem_setOf_eq, row_epi] at h2
  have h2' : (f fun v => q (some v)) ≤ ((q none + ∑ v, p v * q (some v) : ℝ) : WithTop ℝ) ↔
      ∀ i : Fin m, a i none * (q none + ∑ v, p v * q (some v)) + ∑ v, a i (some v) * q (some v) ≤ b i := h2
  rw [h2']
  simp only [Fintype.sum_option, Option.elim]
  apply forall_congr'; intro i
  have he : ∑ v, (a i (some v) + a i none * p v) * q (some v) =
      ∑ v, a i (some v) * q (some v) + a i none * ∑ v, p v * q (some v) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [he]
  constructor <;> intro h <;> linarith

theorem dual_part_msfp3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f) (hfPoly : IsPolyhedralConvex f)
    (hfa : ∀ a, IsPolyhedralConvexArc (fa a))
    (xi0 : A → ℝ) (hxi0 : OptimalFlowMCFP3 tail head fa f xi0) :
    LConvexPolyhedronR (OptimalPotentialSetMSFP3 tail head fa f) ∧
    (((∀ a, IsDualIntegralArc (fa a)) ∧ IsDualIntegralR f) →
      IsIntegralPolyhedron (OptimalPotentialSetMSFP3 tail head fa f) ∧
      ∃ pZ : V → ℤ, (fun v => (pZ v : ℝ)) ∈ OptimalPotentialSetMSFP3 tail head fa f) := by
  have hcore := potential_criterion_msfp3 tail head fa f hf hfPoly hfa
  obtain ⟨p0, hp0⟩ := (hcore.1 xi0 hxi0.1).mp hxi0
  have hpot_set : OptimalPotentialSetMSFP3 tail head fa f =
      {p | IsOptimalPotential tail head fa f xi0 p} := by
    ext p
    simp only [OptimalPotentialSetMSFP3, Set.mem_setOf_eq]
    constructor
    · rintro ⟨xi, hxi, hp⟩
      exact (hcore.2 xi p hxi hp xi0 hxi0.1).mp hxi0
    · intro hp
      exact ⟨xi0, hxi0, hp⟩
  let x0 : V → ℝ := Boundary tail head xi0
  obtain ⟨u0, w0, hu0, hw0⟩ : ∃ u0 : A → ℝ, ∃ w0 : ℝ,
      (∀ a, fa a (xi0 a) = (u0 a : WithTop ℝ)) ∧ f x0 = (w0 : WithTop ℝ) :=
    ⟨fun a => (fa a (xi0 a)).untop (hxi0.1.1 a), (f x0).untop hxi0.1.2,
      fun a => (WithTop.coe_untop _ _).symm, (WithTop.coe_untop _ _).symm⟩
  obtain ⟨m, C, B, hS⟩ := id hfPoly
  choose ma Ca Ba hSa using hfa
  have hC : ∀ (y : V → ℝ) (r : ℝ), f y ≤ (r : WithTop ℝ) ↔
      ∀ i : Fin m, C i none * r + ∑ v, C i (some v) * y v ≤ B i := by
    intro y r
    have := Set.ext_iff.mp hS (epiPoint y r)
    simpa [epiPoint, Fintype.sum_option] using this
  have hCa : ∀ a (t s : ℝ), fa a t ≤ (s : WithTop ℝ) ↔
      ∀ j : Fin (ma a), Ca a j false * t + Ca a j true * s ≤ Ba a j := by
    intro a t s
    have := Set.ext_iff.mp (hSa a) (fun b => cond b s t)
    simp only [Set.mem_setOf_eq, Fintype.sum_bool, cond_true, cond_false] at this
    rw [this]
    exact forall_congr' (fun j => by rw [add_comm])
  -- Index type for the difference constraints: `(A ⊕ A) ⊕ (V × V)`
  let Idx := (A ⊕ A) ⊕ (V × V)
  let dirV (u v w : V) : ℝ := (if w = v then (1 : ℝ) else 0) - (if w = u then (1 : ℝ) else 0)
  let φ_idx : Idx → ℝ → WithTop ℝ
    | .inl (.inl a), t => fa a (xi0 a + t)
    | .inl (.inr a), t => fa a (xi0 a - t)
    | .inr (u, v), t => f (fun w => x0 w + t * dirV u v w)
  let r0_idx : Idx → ℝ
    | .inl (.inl a) => u0 a
    | .inl (.inr a) => u0 a
    | .inr _ => w0
  let Q_idx (idx : Idx) : Prop := ∃ t1 : ℝ, 0 < t1 ∧ φ_idx idx t1 ≠ ⊤
  let u_idx : Idx → V
    | .inl (.inl a) => head a
    | .inl (.inr a) => tail a
    | .inr (_, v) => v
  let v_idx : Idx → V
    | .inl (.inl a) => tail a
    | .inl (.inr a) => head a
    | .inr (u, _) => u
  have hφ0 : ∀ idx : Idx, φ_idx idx 0 = (r0_idx idx : WithTop ℝ) := by
    rintro ((a | a) | ⟨u, v⟩)
    · simpa [φ_idx, r0_idx] using hu0 a
    · simpa [φ_idx, r0_idx] using hu0 a
    · simp [φ_idx, r0_idx, hw0]
  have hray_all : ∀ idx : Idx, Q_idx idx →
      ∃ (c ε : ℝ), 0 < ε ∧
        (∀ t : ℝ, 0 ≤ t → ((r0_idx idx + c * t : ℝ) : WithTop ℝ) ≤ φ_idx idx t) ∧
        (∀ δ : ℝ, 0 ≤ δ → δ ≤ ε → φ_idx idx δ = ((r0_idx idx + c * δ : ℝ) : WithTop ℝ)) ∧
        (∀ s : ℝ, (∀ t : ℝ, 0 ≤ t → (r0_idx idx : WithTop ℝ) ≤ φ_idx idx t + ((- s * t : ℝ) : WithTop ℝ)) ↔ s ≤ c) := by
    rintro ((a | a) | ⟨u, v⟩) hQ
    · refine polyhedral_ray_slope (φ_idx (.inl (.inl a))) (u0 a) (ma a)
        (fun j => Ca a j false) (fun j => Ca a j true)
        (fun j => Ba a j - Ca a j false * xi0 a) (hφ0 (.inl (.inl a))) (fun t r => ?_) hQ
      dsimp only [φ_idx]
      rw [hCa a (xi0 a + t) r]
      exact forall_congr' fun j => ⟨fun h => by linarith, fun h => by linarith⟩
    · refine polyhedral_ray_slope (φ_idx (.inl (.inr a))) (u0 a) (ma a)
        (fun j => - Ca a j false) (fun j => Ca a j true)
        (fun j => Ba a j - Ca a j false * xi0 a) (hφ0 (.inl (.inr a))) (fun t r => ?_) hQ
      dsimp only [φ_idx]
      rw [hCa a (xi0 a - t) r]
      exact forall_congr' fun j => ⟨fun h => by linarith, fun h => by linarith⟩
    · refine polyhedral_ray_slope (φ_idx (.inr (u, v))) w0 m
        (fun i => ∑ w, C i (some w) * dirV u v w) (fun i => C i none)
        (fun i => B i - ∑ w, C i (some w) * x0 w) (hφ0 (.inr (u, v))) (fun t r => ?_) hQ
      dsimp only [φ_idx]
      rw [hC (fun w => x0 w + t * dirV u v w) r]
      apply forall_congr'; intro i
      have hlin : (∑ w, C i (some w) * (x0 w + t * dirV u v w)) =
          (∑ w, C i (some w) * x0 w) + (∑ w, C i (some w) * dirV u v w) * t := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring
      rw [hlin]
      exact ⟨fun h => by linarith, fun h => by linarith⟩
  choose! c_idx ε_idx hε_pos hlow_idx hexact_idx hiff_idx using hray_all
  have hDiff_eq : {p | IsOptimalPotential tail head fa f xi0 p} =
      DiffSet Q_idx u_idx v_idx c_idx := by
    ext p
    simp only [Set.mem_setOf_eq, IsOptimalPotential, DiffSet]
    have harc_iff : (∀ a : A, xi0 a ∈ ArgMinArc (ReducedArcCost tail head fa p a)) ↔
        ∀ a : A, (Q_idx (.inl (.inl a)) → p (head a) - p (tail a) ≤ c_idx (.inl (.inl a))) ∧
          (Q_idx (.inl (.inr a)) → p (tail a) - p (head a) ≤ c_idx (.inl (.inr a))) := by
      apply forall_congr'; intro a
      have hsplit : xi0 a ∈ ArgMinArc (ReducedArcCost tail head fa p a) ↔
          (∀ t : ℝ, 0 ≤ t → (u0 a : WithTop ℝ) ≤ fa a (xi0 a + t) +
            ((- (p (head a) - p (tail a)) * t : ℝ) : WithTop ℝ)) ∧
          (∀ t : ℝ, 0 ≤ t → (u0 a : WithTop ℝ) ≤ fa a (xi0 a - t) +
            ((- (p (tail a) - p (head a)) * t : ℝ) : WithTop ℝ)) := by
        simp only [ArgMinArc, Set.mem_setOf_eq, ReducedArcCost, Coboundary, hu0 a]
        constructor
        · intro h
          refine ⟨fun t ht => ?_, fun t ht => ?_⟩
          · have h1 := h (xi0 a + t)
            cases hfas : fa a (xi0 a + t) with
            | top => simp
            | coe r =>
              rw [hfas, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h1
              rw [← WithTop.coe_add, WithTop.coe_le_coe]
              linarith
          · have h1 := h (xi0 a - t)
            cases hfas : fa a (xi0 a - t) with
            | top => simp
            | coe r =>
              rw [hfas, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h1
              rw [← WithTop.coe_add, WithTop.coe_le_coe]
              linarith
        · rintro ⟨h1, h2⟩ s
          rcases le_total (xi0 a) s with hle | hle
          · have h' := h1 (s - xi0 a) (sub_nonneg.mpr hle)
            rw [add_sub_cancel] at h'
            cases hfas : fa a s with
            | top => simp
            | coe r =>
              rw [hfas, ← WithTop.coe_add, WithTop.coe_le_coe] at h'
              rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
              linarith
          · have h' := h2 (xi0 a - s) (sub_nonneg.mpr hle)
            rw [sub_sub_cancel] at h'
            cases hfas : fa a s with
            | top => simp
            | coe r =>
              rw [hfas, ← WithTop.coe_add, WithTop.coe_le_coe] at h'
              rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
              linarith
      rw [hsplit]
      apply and_congr
      · by_cases hQ : Q_idx (.inl (.inl a))
        · simp only [hQ, true_implies]
          exact hiff_idx (.inl (.inl a)) hQ (p (head a) - p (tail a))
        · simp only [hQ, false_implies, iff_true]
          intro t ht
          rcases eq_or_lt_of_le ht with rfl | ht_pos
          · simp [hu0 a]
          · have htop : fa a (xi0 a + t) = ⊤ := by
              by_contra hne; exact hQ ⟨t, ht_pos, hne⟩
            simp [htop]
      · by_cases hQ : Q_idx (.inl (.inr a))
        · simp only [hQ, true_implies]
          exact hiff_idx (.inl (.inr a)) hQ (p (tail a) - p (head a))
        · simp only [hQ, false_implies, iff_true]
          intro t ht
          rcases eq_or_lt_of_le ht with rfl | ht_pos
          · simp [hu0 a]
          · have htop : fa a (xi0 a - t) = ⊤ := by
              by_contra hne; exact hQ ⟨t, ht_pos, hne⟩
            simp [htop]
    have hbd_iff : x0 ∈ ArgMinR (ReducedBoundaryCost f p) ↔
        ∀ u v : V, Q_idx (.inr (u, v)) → p v - p u ≤ c_idx (.inr (u, v)) := by
      have hG_ne : ReducedBoundaryCost f p x0 ≠ ⊤ := by
        rw [ReducedBoundaryCost, hw0]
        change ((w0 - ∑ v, p v * x0 v : ℝ) : WithTop ℝ) ≠ ⊤
        exact WithTop.coe_ne_top
      have hray_min : x0 ∈ ArgMinR (ReducedBoundaryCost f p) ↔
          ∀ u v : V, ∀ t : ℝ, 0 ≤ t →
            ReducedBoundaryCost f p x0 ≤
              ReducedBoundaryCost f p (fun w => x0 w + t * dirV u v w) := by
        constructor
        · intro h u v t _; exact h _
        · intro h
          exact global_min_of_exchange_rays (ReducedBoundaryCost f p)
            (closed_sublevel _ (poly_reducedBoundary f hfPoly p))
            (mexc_reducedBoundary f hf p) x0 hG_ne h
      rw [hray_min]
      apply forall_congr'; intro u
      apply forall_congr'; intro v
      have hstep : (∀ t : ℝ, 0 ≤ t →
          ReducedBoundaryCost f p x0 ≤
            ReducedBoundaryCost f p (fun w => x0 w + t * dirV u v w)) ↔
          (∀ t : ℝ, 0 ≤ t → (w0 : WithTop ℝ) ≤ φ_idx (.inr (u, v)) t +
            ((- (p v - p u) * t : ℝ) : WithTop ℝ)) := by
        apply forall_congr'; intro t
        apply imp_congr_right; intro ht
        simp only [ReducedBoundaryCost, hw0, φ_idx]
        have hsum : (∑ w, p w * (x0 w + t * dirV u v w)) =
            (∑ w, p w * x0 w) + (p v - p u) * t := by
          simp only [dirV, mul_add, mul_sub, mul_ite, mul_one, mul_zero,
            Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        rw [hsum]
        induction f (fun w => x0 w + t * dirV u v w) using WithTop.recTopCoe with
        | top => simp
        | coe r =>
          change ((w0 - ∑ w, p w * x0 w : ℝ) : WithTop ℝ) ≤
            ((r - (∑ w, p w * x0 w + (p v - p u) * t) : ℝ) : WithTop ℝ) ↔ _
          rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
          exact ⟨fun h => by linarith, fun h => by linarith⟩
      rw [hstep]
      by_cases hQ : Q_idx (.inr (u, v))
      · simp only [hQ, true_implies]
        exact hiff_idx (.inr (u, v)) hQ (p v - p u)
      · simp only [hQ, false_implies, iff_true]
        intro t ht
        rcases eq_or_lt_of_le ht with rfl | ht_pos
        · simp [φ_idx, hw0]
        · have htop : φ_idx (.inr (u, v)) t = ⊤ := by
            by_contra hne; exact hQ ⟨t, ht_pos, hne⟩
          simp [htop]
    rw [harc_iff, hbd_iff]
    constructor
    · rintro ⟨h1, h2⟩ ((a | a) | ⟨u, v⟩)
      · exact (h1 a).1
      · exact (h1 a).2
      · exact h2 u v
    · intro h
      refine ⟨fun a => ⟨h (.inl (.inl a)), h (.inl (.inr a))⟩, fun u v => h (.inr (u, v))⟩
  have hne : (DiffSet Q_idx u_idx v_idx c_idx).Nonempty := by
    rw [← hDiff_eq]
    exact ⟨p0, hp0⟩
  rw [hpot_set, hDiff_eq]
  refine ⟨⟨diffSet_polyhedron _ _ _ _, hne, fun p hp q hq => ⟨diffSet_sup _ _ _ _ hp hq,
    diffSet_inf _ _ _ _ hp hq⟩, fun p hp α => diffSet_trans _ _ _ _ hp α⟩, ?_⟩
  rintro ⟨hdualA, hdualF⟩
  have hc_int : ∀ idx : Idx, Q_idx idx → ∃ n : ℤ, c_idx idx = (n : ℝ) := by
    rintro ((a | a) | ⟨u, v⟩) hQ
    · set ε := ε_idx (.inl (.inl a))
      have hε : 0 < ε := hε_pos (.inl (.inl a)) hQ
      have hex := hexact_idx (.inl (.inl a)) hQ
      have hmid : fa a (xi0 a + ε / 2) =
          ((u0 a + c_idx (.inl (.inl a)) * (ε / 2) : ℝ) : WithTop ℝ) :=
        hex (ε / 2) (by linarith) (by linarith)
      have hend : fa a (xi0 a + ε) =
          ((u0 a + c_idx (.inl (.inl a)) * ε : ℝ) : WithTop ℝ) :=
        hex ε hε.le le_rfl
      obtain ⟨n, hn⟩ := hdualA a (xi0 a + ε / 2) (by rw [hmid]; exact WithTop.coe_ne_top)
      have h1 := hn (xi0 a + ε)
      have h2 := hn (xi0 a)
      rw [hend, hmid] at h1
      rw [hu0 a, hmid] at h2
      change ((u0 a + c_idx (.inl (.inl a)) * ε - (u0 a + c_idx (.inl (.inl a)) * (ε / 2)) : ℝ) : WithTop ℝ) ≥
        (((n : ℝ) * (xi0 a + ε - (xi0 a + ε / 2)) : ℝ) : WithTop ℝ) at h1
      change ((u0 a - (u0 a + c_idx (.inl (.inl a)) * (ε / 2)) : ℝ) : WithTop ℝ) ≥
        (((n : ℝ) * (xi0 a - (xi0 a + ε / 2)) : ℝ) : WithTop ℝ) at h2
      rw [ge_iff_le, WithTop.coe_le_coe] at h1 h2
      exact ⟨n, by nlinarith⟩
    · set ε := ε_idx (.inl (.inr a))
      have hε : 0 < ε := hε_pos (.inl (.inr a)) hQ
      have hex := hexact_idx (.inl (.inr a)) hQ
      have hmid : fa a (xi0 a - ε / 2) =
          ((u0 a + c_idx (.inl (.inr a)) * (ε / 2) : ℝ) : WithTop ℝ) :=
        hex (ε / 2) (by linarith) (by linarith)
      have hend : fa a (xi0 a - ε) =
          ((u0 a + c_idx (.inl (.inr a)) * ε : ℝ) : WithTop ℝ) :=
        hex ε hε.le le_rfl
      obtain ⟨n, hn⟩ := hdualA a (xi0 a - ε / 2) (by rw [hmid]; exact WithTop.coe_ne_top)
      have h1 := hn (xi0 a - ε)
      have h2 := hn (xi0 a)
      rw [hend, hmid] at h1
      rw [hu0 a, hmid] at h2
      change ((u0 a + c_idx (.inl (.inr a)) * ε - (u0 a + c_idx (.inl (.inr a)) * (ε / 2)) : ℝ) : WithTop ℝ) ≥
        (((n : ℝ) * (xi0 a - ε - (xi0 a - ε / 2)) : ℝ) : WithTop ℝ) at h1
      change ((u0 a - (u0 a + c_idx (.inl (.inr a)) * (ε / 2)) : ℝ) : WithTop ℝ) ≥
        (((n : ℝ) * (xi0 a - (xi0 a - ε / 2)) : ℝ) : WithTop ℝ) at h2
      rw [ge_iff_le, WithTop.coe_le_coe] at h1 h2
      exact ⟨-n, by push_cast; nlinarith⟩
    · set ε := ε_idx (.inr (u, v))
      have hε : 0 < ε := hε_pos (.inr (u, v)) hQ
      have hex := hexact_idx (.inr (u, v)) hQ
      let xmid : V → ℝ := fun w => x0 w + (ε / 2) * dirV u v w
      let xend : V → ℝ := fun w => x0 w + ε * dirV u v w
      have hmid : f xmid = ((w0 + c_idx (.inr (u, v)) * (ε / 2) : ℝ) : WithTop ℝ) :=
        hex (ε / 2) (by linarith) (by linarith)
      have hend : f xend = ((w0 + c_idx (.inr (u, v)) * ε : ℝ) : WithTop ℝ) :=
        hex ε hε.le le_rfl
      obtain ⟨yZ, hyZ⟩ := hdualF xmid (by rw [hmid]; exact WithTop.coe_ne_top)
      have h1 := hyZ xend
      have h2 := hyZ x0
      rw [hend, hmid] at h1
      rw [hw0, hmid] at h2
      change ((w0 + c_idx (.inr (u, v)) * ε - (w0 + c_idx (.inr (u, v)) * (ε / 2)) : ℝ) : WithTop ℝ) ≥
        (((∑ w, (yZ w : ℝ) * (xend w - xmid w)) : ℝ) : WithTop ℝ) at h1
      change ((w0 - (w0 + c_idx (.inr (u, v)) * (ε / 2)) : ℝ) : WithTop ℝ) ≥
        (((∑ w, (yZ w : ℝ) * (x0 w - xmid w)) : ℝ) : WithTop ℝ) at h2
      rw [ge_iff_le, WithTop.coe_le_coe] at h1 h2
      have hs1 : (∑ w, (yZ w : ℝ) * (xend w - xmid w)) = ((yZ v : ℝ) - (yZ u : ℝ)) * (ε / 2) := by
        have hd : ∀ w, (yZ w : ℝ) * (xend w - xmid w) =
            (if w = v then (yZ w : ℝ) * (ε / 2) else 0) - (if w = u then (yZ w : ℝ) * (ε / 2) else 0) := by
          intro w; dsimp [xend, xmid, dirV]; split_ifs <;> ring
        simp_rw [hd]
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true]
        ring
      have hs2 : (∑ w, (yZ w : ℝ) * (x0 w - xmid w)) = - (((yZ v : ℝ) - (yZ u : ℝ)) * (ε / 2)) := by
        have hd : ∀ w, (yZ w : ℝ) * (x0 w - xmid w) =
            (if w = u then (yZ w : ℝ) * (ε / 2) else 0) - (if w = v then (yZ w : ℝ) * (ε / 2) else 0) := by
          intro w; dsimp [xmid, dirV]; split_ifs <;> ring
        simp_rw [hd]
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true]
        ring
      rw [hs1] at h1
      rw [hs2] at h2
      refine ⟨yZ v - yZ u, ?_⟩
      push_cast
      nlinarith
  refine ⟨diffSet_integral _ _ _ _ hc_int, ?_⟩
  obtain ⟨p, hp⟩ := hne
  exact ⟨fun v => ⌊p v⌋, diffSet_floor _ _ _ _ hc_int hp⟩

end DualPart

/-! ## Section 5: Primal structure and integrality of `BoundaryOptSetMSFP3` -/

section PrimalPart
set_option linter.unusedSectionVars false

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

lemma boundary_lin (tail head : A → V) (d g : A → ℝ) (e : ℝ) (v : V) :
    Boundary tail head (fun b => d b + e * g b) v =
      Boundary tail head d v + e * Boundary tail head g v := by
  simp only [Boundary, Finset.sum_add_distrib, ← Finset.mul_sum]; ring

def aT (tail head : A → V) : A ⊕ A → V
  | .inl a => tail a
  | .inr a => head a

def aH (tail head : A → V) : A ⊕ A → V
  | .inl a => head a
  | .inr a => tail a

def evA : A ⊕ A → A → ℝ
  | .inl a => fun b => if a = b then 1 else 0
  | .inr a => fun b => if a = b then -1 else 0

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

def StepFlow (tail head : A → V) (xix xiy : A → ℝ) (u v : V) : Prop :=
  ∃ e : A ⊕ A, aT tail head e = u ∧ aH tail head e = v ∧
    match e with
    | .inl a => xiy a < xix a
    | .inr a => xix a < xiy a

lemma reach_chi (tail head : A → V) (xix xiy : A → ℝ) (i u : V)
    (h : Relation.ReflTransGen (StepFlow tail head xix xiy) i u) :
    ∃ χ : A → ℝ,
      (∀ v : V, Boundary tail head χ v = (if v = i then (1:ℝ) else 0) - (if v = u then 1 else 0)) ∧
      (∀ a : A, (0 < χ a → xiy a < xix a) ∧ (χ a < 0 → xix a < xiy a)) := by
  induction h with
  | refl =>
    refine ⟨fun _ => 0, fun v => ?_, fun a => ⟨fun h => by linarith, fun h => by linarith⟩⟩
    simp [Boundary]
  | @tail u w _ hstep ih =>
    obtain ⟨χ, hχbd, hχsign⟩ := ih
    obtain ⟨e, heT, heH, heIneq⟩ := hstep
    refine ⟨fun b => χ b + evA e b, fun v => ?_, fun b => ?_⟩
    · have hlin := boundary_lin tail head χ (evA e) 1 v
      simp only [one_mul] at hlin
      rw [hlin, hχbd v, boundary_evA, heT, heH]
      have h1 : (if u = v then (1:ℝ) else 0) = (if v = u then 1 else 0) := by
        by_cases h : u = v <;> simp [h, eq_comm]
      have h2 : (if w = v then (1:ℝ) else 0) = (if v = w then 1 else 0) := by
        by_cases h : w = v <;> simp [h, eq_comm]
      linarith
    · cases e with
      | inl a =>
        dsimp only at heIneq
        by_cases hab : a = b
        · subst hab
          have hnot_neg : ¬ (χ a < 0) := fun hneg => not_lt_of_gt heIneq ((hχsign a).2 hneg)
          have hpos : 0 < χ a + evA (.inl a) a := by simp [evA]; linarith
          exact ⟨fun _ => heIneq, fun hlt => absurd hlt (not_lt_of_gt hpos)⟩
        · simp only [evA, if_neg hab, add_zero]
          exact hχsign b
      | inr a =>
        dsimp only at heIneq
        by_cases hab : a = b
        · subst hab
          have hnot_pos : ¬ (0 < χ a) := fun hpos => not_lt_of_gt heIneq ((hχsign a).1 hpos)
          have hneg : χ a + evA (.inr a) a < 0 := by simp [evA]; linarith
          exact ⟨fun hgt => absurd hgt (not_lt_of_gt hneg), fun _ => heIneq⟩
        · simp only [evA, if_neg hab, add_zero]
          exact hχsign b

lemma exists_reach_neg (tail head : A → V) (xix xiy : A → ℝ) (i : V)
    (hi : 0 < Boundary tail head xix i - Boundary tail head xiy i) :
    ∃ j : V, Relation.ReflTransGen (StepFlow tail head xix xiy) i j ∧
      Boundary tail head xix j - Boundary tail head xiy j < 0 := by
  by_contra hcon
  push_neg at hcon
  let R : Finset V := Finset.univ.filter (fun v => Relation.ReflTransGen (StepFlow tail head xix xiy) i v)
  let indR : V → ℝ := fun v => if v ∈ R then 1 else 0
  let d : A → ℝ := fun a => xix a - xiy a
  have hbd_sub : ∀ v : V, Boundary tail head d v = Boundary tail head xix v - Boundary tail head xiy v := by
    intro v
    have hlin := boundary_lin tail head xix xiy (-1) v
    have heq : d = fun b => xix b + (-1) * xiy b := by funext b; dsimp [d]; ring
    rw [heq, hlin]
    ring
  have hiR : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ i, Relation.ReflTransGen.refl⟩
  have hsum_pos : 0 < ∑ v : V, indR v * Boundary tail head d v := by
    have hnonneg : ∀ v ∈ Finset.univ, 0 ≤ indR v * Boundary tail head d v := by
      intro v _
      dsimp [indR]
      split_ifs with hv
      · rw [one_mul, hbd_sub]
        exact hcon v (Finset.mem_filter.mp hv).2
      · simp
    have hipos : 0 < indR i * Boundary tail head d i := by
      simp only [indR, if_pos hiR, one_mul, hbd_sub]
      exact hi
    exact Finset.sum_pos' hnonneg ⟨i, Finset.mem_univ i, hipos⟩
  have hpair := bnd_pair tail head indR d
  have harc_nonpos : ∀ a ∈ Finset.univ, d a * Coboundary tail head indR a ≤ 0 := by
    intro a _
    simp only [Coboundary, indR]
    by_cases ht : tail a ∈ R <;> by_cases hh : head a ∈ R
    · simp [ht, hh]
    · simp only [if_pos ht, if_neg hh, sub_zero, mul_one]
      have hnot : ¬ (xiy a < xix a) := by
        intro hlt
        apply hh
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Relation.ReflTransGen.tail (Finset.mem_filter.mp ht).2 ⟨.inl a, rfl, rfl, hlt⟩⟩
      dsimp [d]; linarith
    · simp only [if_neg ht, if_pos hh, zero_sub, mul_neg, mul_one, Left.neg_nonpos_iff]
      have hnot : ¬ (xix a < xiy a) := by
        intro hlt
        apply ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Relation.ReflTransGen.tail (Finset.mem_filter.mp hh).2 ⟨.inr a, rfl, rfl, hlt⟩⟩
      dsimp [d]; linarith
    · simp [ht, hh]
  have hsum_nonpos : ∑ a : A, d a * Coboundary tail head indR a ≤ 0 :=
    Finset.sum_nonpos harc_nonpos
  linarith

theorem primal_part_msfp3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f) (hfPoly : IsPolyhedralConvex f)
    (hfa : ∀ a, IsPolyhedralConvexArc (fa a))
    (xi0 : A → ℝ) (hxi0 : OptimalFlowMCFP3 tail head fa f xi0) :
    M2ConvexPolyhedronR (BoundaryOptSetMSFP3 tail head fa f) ∧
    (((∀ a, IsDomainIntegerArc (fa a)) ∧ IsDomainIntegerR f) →
      IsIntegralPolyhedron (BoundaryOptSetMSFP3 tail head fa f) ∧
      ∃ xiZ : A → ℤ, OptimalFlowMCFP3 tail head fa f (fun a => (xiZ a : ℝ))) := by
  have hcore := potential_criterion_msfp3 tail head fa f hf hfPoly hfa
  obtain ⟨p0, hp0⟩ := (hcore.1 xi0 hxi0.1).mp hxi0
  let x0 : V → ℝ := Boundary tail head xi0
  obtain ⟨u0, w0, hu0, hw0⟩ : ∃ u0 : A → ℝ, ∃ w0 : ℝ,
      (∀ a, fa a (xi0 a) = (u0 a : WithTop ℝ)) ∧ f x0 = (w0 : WithTop ℝ) :=
    ⟨fun a => (fa a (xi0 a)).untop (hxi0.1.1 a), (f x0).untop hxi0.1.2,
      fun a => (WithTop.coe_untop _ _).symm, (WithTop.coe_untop _ _).symm⟩
  -- Characterize optimal flows via p0
  have hopt_iff : ∀ xi : A → ℝ,
      OptimalFlowMCFP3 tail head fa f xi ↔ IsOptimalPotential tail head fa f xi p0 := by
    intro xi
    constructor
    · intro hxi
      exact (hcore.2 xi0 p0 hxi0 hp0 xi hxi.1).mp hxi
    · intro hp
      have hfeas : FeasibleFlowMCFP3 tail head fa f xi := by
        refine ⟨fun a => ?_, ?_⟩
        · have hle := hp.1 a (xi0 a)
          have hne : ReducedArcCost tail head fa p0 a (xi0 a) ≠ ⊤ := by
            rw [ReducedArcCost, hu0 a, ← WithTop.coe_add]
            exact WithTop.coe_ne_top
          have hne' := ne_top_of_le_ne_top hne hle
          intro htop; apply hne'
          rw [ReducedArcCost, htop, WithTop.top_add]
        · have hle := hp.2 x0
          have hne : ReducedBoundaryCost f p0 x0 ≠ ⊤ := by
            rw [ReducedBoundaryCost, hw0]
            change ((w0 - ∑ v, p0 v * x0 v : ℝ) : WithTop ℝ) ≠ ⊤
            exact WithTop.coe_ne_top
          have hne' := ne_top_of_le_ne_top hne hle
          intro htop; apply hne'
          rw [ReducedBoundaryCost, htop]
          rfl
      exact (hcore.2 xi0 p0 hxi0 hp0 xi hfeas).mpr hp
  let Ia (a : A) : Set ℝ := ArgMinArc (ReducedArcCost tail head fa p0 a)
  let P1 : Set (V → ℝ) := {x : V → ℝ | ∃ xi : A → ℝ, (∀ a : A, xi a ∈ Ia a) ∧ x = Boundary tail head xi}
  let P2 : Set (V → ℝ) := ArgMinR (ReducedBoundaryCost f p0)
  have hBnd_eq : BoundaryOptSetMSFP3 tail head fa f = P1 ∩ P2 := by
    ext x
    simp only [BoundaryOptSetMSFP3, Set.mem_setOf_eq, Set.mem_inter_iff, P1, P2, hopt_iff,
      IsOptimalPotential]
    constructor
    · rintro ⟨xi, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨xi, h1, rfl⟩, h2⟩
    · rintro ⟨⟨xi, h1, rfl⟩, h2⟩
      exact ⟨xi, ⟨h1, h2⟩, rfl⟩
  -- Prove MConvexPolyhedronR P2
  let μ : ℝ := w0 - ∑ v, p0 v * x0 v
  have hGx0 : ReducedBoundaryCost f p0 x0 = (μ : WithTop ℝ) := by
    simp [ReducedBoundaryCost, hw0, μ]
  have hP2_iff : ∀ y : V → ℝ, y ∈ P2 ↔ ReducedBoundaryCost f p0 y ≤ (μ : WithTop ℝ) := by
    intro y
    simp only [P2, ArgMinR, Set.mem_setOf_eq]
    constructor
    · intro hy; rw [← hGx0]; exact hy x0
    · intro hy q; exact hy.trans (hGx0 ▸ hp0.2 q)
  have hP2_low : ∀ y : V → ℝ, (μ : WithTop ℝ) ≤ ReducedBoundaryCost f p0 y :=
    fun y => hGx0 ▸ hp0.2 y
  have hP2_poly : IsPolyhedron P2 := by
    obtain ⟨m, a, b, hab⟩ := poly_reducedBoundary f hfPoly p0
    refine ⟨m, fun i v => a i (some v), fun i => b i - a i none * μ, ?_⟩
    ext y
    simp only [hP2_iff, Set.mem_setOf_eq]
    have h := Set.ext_iff.mp hab (epiPoint y μ)
    simp only [Set.mem_setOf_eq, row_epi] at h
    have h' : ReducedBoundaryCost f p0 y ≤ (μ : WithTop ℝ) ↔
        ∀ i : Fin m, a i none * μ + ∑ v, a i (some v) * y v ≤ b i := h
    rw [h']
    exact forall_congr' fun i => ⟨fun hle => by linarith, fun hle => by linarith⟩
  have hP2_mconv : MConvexPolyhedronR P2 := by
    refine ⟨hP2_poly, fun x hx y hy i hi => ?_⟩
    have hGx : ReducedBoundaryCost f p0 x = (μ : WithTop ℝ) :=
      le_antisymm ((hP2_iff x).mp hx) (hP2_low x)
    have hGy : ReducedBoundaryCost f p0 y = (μ : WithTop ℝ) :=
      le_antisymm ((hP2_iff y).mp hy) (hP2_low y)
    have hx_dom : x ∈ DomR (ReducedBoundaryCost f p0) := by
      simp [DomR, hGx]
    have hy_dom : y ∈ DomR (ReducedBoundaryCost f p0) := by
      simp [DomR, hGy]
    have hi_pos : i ∈ SuppPosR x y := Finset.mem_filter.mpr ⟨Finset.mem_univ i, sub_pos.mp hi⟩
    obtain ⟨j, hj, α0, hα0, hexc⟩ :=
      mexc_reducedBoundary f hf p0 x hx_dom y hy_dom i hi_pos
    have hj_neg : x j - y j < 0 := sub_neg.mpr (Finset.mem_filter.mp hj).2
    refine ⟨j, hj_neg, α0, hα0, fun α h0 h1 => ?_⟩
    have hα := hexc α h0 h1
    set x' : V → ℝ := fun v => x v - α * ((if v = i then (1:ℝ) else 0) - (if v = j then 1 else 0))
    set y' : V → ℝ := fun v => y v + α * ((if v = i then (1:ℝ) else 0) - (if v = j then 1 else 0))
    have hx'_eq : (fun w => x w - α * (if w = i then (1:ℝ) else 0) + α * (if w = j then (1:ℝ) else 0)) = x' := by
      funext w; dsimp [x']; ring
    have hy'_eq : (fun w => y w + α * (if w = i then (1:ℝ) else 0) - α * (if w = j then (1:ℝ) else 0)) = y' := by
      funext w; dsimp [y']; ring
    rw [hx'_eq, hy'_eq, hGx, hGy, ge_iff_le] at hα
    have h1' : ReducedBoundaryCost f p0 x' ≤ (μ : WithTop ℝ) := by
      have h2 := (add_le_add le_rfl (hP2_low y')).trans hα
      exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp h2
    have h2' : ReducedBoundaryCost f p0 y' ≤ (μ : WithTop ℝ) := by
      have h2 := (add_le_add (hP2_low x') le_rfl).trans hα
      exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp h2
    exact ⟨(hP2_iff x').mpr h1', (hP2_iff y').mpr h2'⟩
  -- Prove MConvexPolyhedronR P1
  let μa (a : A) : ℝ := u0 a + Coboundary tail head p0 a * xi0 a
  have hGa0 : ∀ a : A, ReducedArcCost tail head fa p0 a (xi0 a) = (μa a : WithTop ℝ) := by
    intro a; simp [ReducedArcCost, hu0 a, μa]
  have hIa_iff : ∀ a : A, ∀ t : ℝ, t ∈ Ia a ↔
      fa a t ≤ ((μa a - Coboundary tail head p0 a * t : ℝ) : WithTop ℝ) := by
    intro a t
    simp only [Ia, ArgMinArc, Set.mem_setOf_eq]
    have h1 : (∀ s, ReducedArcCost tail head fa p0 a t ≤ ReducedArcCost tail head fa p0 a s) ↔
        ReducedArcCost tail head fa p0 a t ≤ (μa a : WithTop ℝ) := by
      constructor
      · intro ht; rw [← hGa0 a]; exact ht (xi0 a)
      · intro ht s; exact ht.trans (hGa0 a ▸ hp0.1 a s)
    rw [h1, ReducedArcCost]
    induction fa a t using WithTop.recTopCoe with
    | top =>
      rw [WithTop.top_add]
      exact ⟨fun h => absurd (WithTop.top_le_iff.mp h) WithTop.coe_ne_top,
        fun h => absurd (WithTop.top_le_iff.mp h) WithTop.coe_ne_top⟩
    | coe r =>
      rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
      exact ⟨fun h => by linarith, fun h => by linarith⟩
  choose ma Ca Ba hSa using hfa
  have hIa_lin : ∀ a : A, ∀ t : ℝ, t ∈ Ia a ↔
      ∀ j : Fin (ma a),
        (Ca a j false - Ca a j true * Coboundary tail head p0 a) * t ≤
          Ba a j - Ca a j true * μa a := by
    intro a t
    rw [hIa_iff]
    have h := Set.ext_iff.mp (hSa a) (fun b => cond b (μa a - Coboundary tail head p0 a * t) t)
    simp only [Set.mem_setOf_eq, Fintype.sum_bool, cond_true, cond_false] at h
    rw [h]
    exact forall_congr' fun j => ⟨fun hle => by linarith, fun hle => by linarith⟩
  have hIa_conv : ∀ a : A, ∀ t1 ∈ Ia a, ∀ t2 ∈ Ia a, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      (1 - θ) * t1 + θ * t2 ∈ Ia a := by
    intro a t1 ht1 t2 ht2 θ hθ0 hθ1
    rw [hIa_lin] at ht1 ht2 ⊢
    intro j
    have h1 := ht1 j
    have h2 := ht2 j
    nlinarith
  have hP1_poly : IsPolyhedron P1 := by
    let Isys := (Σ a : A, Fin (ma a)) ⊕ V ⊕ V
    let Csys : Isys → V → ℝ
      | .inl _, _ => 0
      | .inr (.inl v), w => if w = v then 1 else 0
      | .inr (.inr v), w => if w = v then -1 else 0
    let Dsys : Isys → A → ℝ
      | .inl ⟨a, j⟩, b => if b = a then Ca a j false - Ca a j true * Coboundary tail head p0 a else 0
      | .inr (.inl v), b => - ((if tail b = v then (1:ℝ) else 0) - (if head b = v then 1 else 0))
      | .inr (.inr v), b => (if tail b = v then (1:ℝ) else 0) - (if head b = v then 1 else 0)
    let Esys : Isys → ℝ
      | .inl ⟨a, j⟩ => Ba a j - Ca a j true * μa a
      | .inr _ => 0
    have h := isPolyhedron_exists_fintype Csys Dsys Esys
    convert h using 1
    ext x
    simp only [P1, Set.mem_setOf_eq]
    apply exists_congr; intro xi
    have hbd_sum : ∀ v : V,
        (∑ b : A, ((if tail b = v then (1:ℝ) else 0) - (if head b = v then 1 else 0)) * xi b) =
          Boundary tail head xi v := by
      intro v
      simp only [Boundary, Finset.sum_filter, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    constructor
    · rintro ⟨h1, rfl⟩
      rintro (⟨a, j⟩ | v | v)
      · simp only [Csys, Dsys, Esys, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact (hIa_lin a (xi a)).mp (h1 a) j
      · simp only [Csys, Dsys, Esys, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true, neg_mul, Finset.sum_neg_distrib, hbd_sum]
        linarith
      · simp only [Csys, Dsys, Esys, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true, hbd_sum]
        linarith
    · intro hsys
      refine ⟨fun a => (hIa_lin a (xi a)).mpr fun j => ?_, ?_⟩
      · have hj := hsys (.inl ⟨a, j⟩)
        simpa [Csys, Dsys, Esys] using hj
      · funext v
        have hv1 := hsys (.inr (.inl v))
        have hv2 := hsys (.inr (.inr v))
        simp only [Csys, Dsys, Esys, ite_mul, one_mul, zero_mul, neg_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib, hbd_sum] at hv1 hv2
        linarith
  have hP1_mconv : MConvexPolyhedronR P1 := by
    refine ⟨hP1_poly, fun x ⟨xix, hxix, hxx⟩ y ⟨xiy, hxiy, hyy⟩ i hi => ?_⟩
    rw [hxx, hyy] at hi
    obtain ⟨j, hreach, hj_neg⟩ := exists_reach_neg tail head xix xiy i hi
    obtain ⟨χ, hχbd, hχsign⟩ := reach_chi tail head xix xiy i j hreach
    let arcBnd (a : A) : ℝ := if χ a = 0 then 1 else |xix a - xiy a| / |χ a|
    have harcBnd : ∀ a : A, 0 < arcBnd a := by
      intro a
      dsimp [arcBnd]
      split_ifs with h0
      · norm_num
      · rcases lt_or_gt_of_ne h0 with hneg | hpos
        · have hlt := (hχsign a).2 hneg
          exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hlt.ne)) (abs_pos.mpr h0)
        · have hlt := (hχsign a).1 hpos
          exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hlt.ne')) (abs_pos.mpr h0)
    obtain ⟨α0, hα0_pos, hα0B⟩ := finite_positive_bound Finset.univ arcBnd (fun a _ => harcBnd a)
    refine ⟨j, by rwa [hxx, hyy], α0, hα0_pos, fun α h0 h1 => ?_⟩
    have hstep_in : ∀ a : A,
        xix a - α * χ a ∈ Ia a ∧ xiy a + α * χ a ∈ Ia a := by
      intro a
      by_cases hχ0 : χ a = 0
      · simp [hχ0, hxix a, hxiy a]
      · have hb := h1.trans (hα0B a (Finset.mem_univ a))
        simp only [arcBnd, if_neg hχ0] at hb
        let θ : ℝ := (α * χ a) / (xix a - xiy a)
        have hθ0 : 0 ≤ θ := by
          rcases lt_or_gt_of_ne hχ0 with hneg | hpos
          · have hlt := (hχsign a).2 hneg
            exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h0 hneg.le) (sub_nonpos.mpr hlt.le)
          · have hlt := (hχsign a).1 hpos
            exact div_nonneg (mul_nonneg h0 hpos.le) (sub_nonneg.mpr hlt.le)
        have hθ1 : θ ≤ 1 := by
          rcases lt_or_gt_of_ne hχ0 with hneg | hpos
          · have hlt := (hχsign a).2 hneg
            have hm := (le_div_iff₀ (abs_pos.mpr hχ0)).mp hb
            rw [abs_of_neg hneg, abs_of_neg (sub_neg.mpr hlt)] at hm
            rw [div_le_iff_of_neg (sub_neg.mpr hlt)]
            linarith
          · have hlt := (hχsign a).1 hpos
            have hm := (le_div_iff₀ (abs_pos.mpr hχ0)).mp hb
            rw [abs_of_pos hpos, abs_of_pos (sub_pos.mpr hlt)] at hm
            rw [div_le_one (sub_pos.mpr hlt)]
            linarith
        have hne_diff : xix a - xiy a ≠ 0 := by
          rcases lt_or_gt_of_ne hχ0 with hneg | hpos
          · exact sub_ne_zero.mpr ((hχsign a).2 hneg).ne
          · exact sub_ne_zero.mpr ((hχsign a).1 hpos).ne'
        have he1 : xix a - α * χ a = (1 - θ) * xix a + θ * xiy a := by
          dsimp [θ]; field_simp; ring
        have he2 : xiy a + α * χ a = (1 - (1 - θ)) * xix a + (1 - θ) * xiy a := by
          dsimp [θ]; field_simp; ring
        rw [he1, he2]
        exact ⟨hIa_conv a (xix a) (hxix a) (xiy a) (hxiy a) θ hθ0 hθ1,
          hIa_conv a (xix a) (hxix a) (xiy a) (hxiy a) (1 - θ) (by linarith) (by linarith)⟩
    refine ⟨⟨fun a => xix a - α * χ a, fun a => (hstep_in a).1, ?_⟩,
      ⟨fun a => xiy a + α * χ a, fun a => (hstep_in a).2, ?_⟩⟩
    · funext v
      have hlin := boundary_lin tail head xix χ (-α) v
      have heq : (fun b => xix b - α * χ b) = (fun b => xix b + (-α) * χ b) := by funext b; ring
      rw [heq, hlin, hxx, hχbd v]
      ring
    · funext v
      rw [boundary_lin tail head xiy χ α v, hyy, hχbd v]
  refine ⟨⟨P1, P2, hP1_mconv, hP2_mconv, hBnd_eq⟩, ?_⟩
  rintro ⟨hdomA, hdomF⟩
  have hBnd_conv : Convex ℝ (BoundaryOptSetMSFP3 tail head fa f) := by
    obtain ⟨m1, a1, b1, h1⟩ := hP1_poly
    obtain ⟨m2, a2, b2, h2⟩ := hP2_poly
    rw [hBnd_eq, h1, h2]
    intro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ s t hs ht hst
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx1 hx2 hy1 hy2 ⊢
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hsum : (∑ w, a1 i w * (s • x + t • y) w) =
          s * (∑ w, a1 i w * x w) + t * (∑ w, a1 i w * y w) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> exact Finset.sum_congr rfl fun w _ => by ring
      rw [hsum]
      have hle1 := mul_le_mul_of_nonneg_left (hx1 i) hs
      have hle2 := mul_le_mul_of_nonneg_left (hy1 i) ht
      have hsb : s * b1 i + t * b1 i = b1 i := by
        calc s * b1 i + t * b1 i = (s + t) * b1 i := by ring
          _ = b1 i := by rw [hst, one_mul]
      linarith
    · have hsum : (∑ w, a2 i w * (s • x + t • y) w) =
          s * (∑ w, a2 i w * x w) + t * (∑ w, a2 i w * y w) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> exact Finset.sum_congr rfl fun w _ => by ring
      rw [hsum]
      have hle1 := mul_le_mul_of_nonneg_left (hx2 i) hs
      have hle2 := mul_le_mul_of_nonneg_left (hy2 i) ht
      have hsb : s * b2 i + t * b2 i = b2 i := by
        calc s * b2 i + t * b2 i = (s + t) * b2 i := by ring
          _ = b2 i := by rw [hst, one_mul]
      linarith
  have hBnd_int : BoundaryOptSetMSFP3 tail head fa f ⊆
      {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)} := by
    rintro x ⟨xi, hxi, rfl⟩
    exact hdomF (Boundary tail head xi) hxi.1.2
  have hIntPoly : IsIntegralPolyhedron (BoundaryOptSetMSFP3 tail head fa f) := by
    unfold IsIntegralPolyhedron
    rw [Set.inter_eq_self_of_subset_left hBnd_int, hBnd_conv.convexHull_eq]
  have hxi0_int : ∀ a : A, ∃ k : ℤ, xi0 a = (k : ℝ) :=
    fun a => hdomA a (xi0 a) (hxi0.1.1 a)
  choose xiZ hxiZ using hxi0_int
  refine ⟨hIntPoly, xiZ, ?_⟩
  have heq : (fun a => (xiZ a : ℝ)) = xi0 := by
    funext a; exact (hxiZ a).symm
  rwa [heq]

end PrimalPart

end DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
open DiscreteConvex.NetworkFlowsB
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem solution (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (hf : MExchangeAxiomR f) (hfPoly : IsPolyhedralConvex f)
    (hfa : ∀ a, IsPolyhedralConvexArc (fa a))
    (hopt : ∃ xi, OptimalFlowMCFP3 tail head fa f xi) :
    M2ConvexPolyhedronR (BoundaryOptSetMSFP3 tail head fa f) ∧
    LConvexPolyhedronR (OptimalPotentialSetMSFP3 tail head fa f) ∧
    (((∀ a, IsDomainIntegerArc (fa a)) ∧ IsDomainIntegerR f) →
      IsIntegralPolyhedron (BoundaryOptSetMSFP3 tail head fa f) ∧
      ∃ xiZ : A → ℤ, OptimalFlowMCFP3 tail head fa f (fun a => (xiZ a : ℝ))) ∧
    (((∀ a, IsDualIntegralArc (fa a)) ∧ IsDualIntegralR f) →
      IsIntegralPolyhedron (OptimalPotentialSetMSFP3 tail head fa f) ∧
      ∃ pZ : V → ℤ, (fun v => (pZ v : ℝ)) ∈ OptimalPotentialSetMSFP3 tail head fa f) := by
  obtain ⟨xi0, hxi0⟩ := hopt
  obtain ⟨hM2, hPrim⟩ := primal_part_msfp3 tail head fa f hf hfPoly hfa xi0 hxi0
  obtain ⟨hL, hDual⟩ := dual_part_msfp3 tail head fa f hf hfPoly hfa xi0 hxi0
  exact ⟨hM2, hL, hPrim, hDual⟩
