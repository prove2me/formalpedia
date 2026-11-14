-- Prove2me | solution 1 for CostSharingPNE.Char.theorem_1_only_if
-- status  : ACCEPTED   (prove)
-- author  : @Albert
-- created : 2026-11-13T10:46:52.548791+00:00
-- url     : https://prove2.me/submissions/76f786d0-ac71-4010-a296-6dd9cf8c8789

import Definitions.Def_CostSharingPNE_Char_Basis
import Theorems.Thm_CostSharingPNE_Char_lemma_7
import Theorems.Thm_CostSharingPNE_Char_lemma_8
import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Theorems.Thm_CostSharingPNE_Char_corollary_1
import Theorems.Thm_CostSharingPNE_Char_lemma_5
import Theorems.Thm_CostSharingPNE_Char_lemma_13

open CostSharingPNE.Char
open scoped BigOperators

private lemma basisSum {n : ℕ} (ω : WeightSystem n) (V : Welfare n)
    (i : Fin n) (S : Finset (Fin n)) :
    (∑ T ∈ coalitions V, mobius V T * gwsvBasis ω T i S) = gwsv ω V i S := by
  classical
  unfold gwsv
  let A := coalitions V
  let B := S.powerset.filter (fun T => i ∈ tbar ω T)
  calc
    _ = ∑ T ∈ A ∩ B, mobius V T * gwsvBasis ω T i S := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro T _ hn
      have hB : T ∉ B := fun h => hn (Finset.mem_inter.mpr ⟨‹T ∈ A›,h⟩)
      have hnot : ¬ (i ∈ tbar ω T ∧ T ⊆ S) := by
        intro h
        exact hB (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.2,h.1⟩)
      simp [gwsvBasis,hnot]
    _ = ∑ T ∈ A ∩ B, (ω.lam i / ∑ j ∈ tbar ω T, ω.lam j) * mobius V T := by
      apply Finset.sum_congr rfl
      intro T h
      have hb := Finset.mem_filter.mp (Finset.mem_inter.mp h).2
      simp [gwsvBasis,hb.2,Finset.mem_powerset.mp hb.1,mul_comm]
    _ = ∑ T ∈ B, (ω.lam i / ∑ j ∈ tbar ω T, ω.lam j) * mobius V T := by
      apply Finset.sum_subset Finset.inter_subset_right
      intro T h hn
      have hm := (Finset.mem_filter.mp h).2
      have hne : T.Nonempty := by
        by_contra h0
        have he := Finset.not_nonempty_iff_eq_empty.mp h0
        simp [he,tbar] at hm
      have hz : mobius V T = 0 := by
        by_contra h0
        apply hn
        exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,h0⟩,h⟩
      simp [hz]

theorem assembleNecessity {n : ℕ} (𝕎 : Set (Welfare n)) (f : Welfare n → Rule n)
    (Ω : Welfare n → Finset (Fin n) → WeightSystem n)
    (hdecomp : ∀ W ∈ 𝕎, ∀ S : Finset (Fin n), ∀ i ∈ S,
      f W i S = ∑ T ∈ coalitions (distributed (f W)),
        mobius (distributed (f W)) T * gwsvBasis (Ω W T) T i S)
    (ω : WeightSystem n)
    (hcommon : ∀ W ∈ 𝕎, ∀ T ∈ coalitions (distributed (f W)), ∀ i S,
      gwsvBasis (Ω W T) T i S = gwsvBasis ω T i S) :
    ∀ W ∈ 𝕎, ∀ S : Finset (Fin n), ∀ i ∈ S,
      f W i S = gwsv ω (distributed (f W)) i S := by
  intro W hW S i hi
  rw [hdecomp W hW S i hi, ← basisSum]
  exact Finset.sum_congr rfl (fun T hT => congrArg (_ * ·) (hcommon W hW T hT i S))

open CostSharingPNE.Char

private def trimRule {n : ℕ} (g : Rule n) : Rule n :=
  fun i S => if i ∈ S then g i S else 0

private lemma utility_normalize {n m : ℕ} (W : Fin m → Welfare n)
    (f : Welfare n → Rule n) (a : Fin n → Finset (Fin m)) (i : Fin n) :
    utility W (fun V => trimRule (f V)) a i = utility W f a i := by
  apply Finset.sum_congr rfl
  intro r hr
  have hi : i ∈ players a r := by simp [players, hr]
  simp [trimRule, hi]

private lemma localNormalize {n : ℕ} {𝕎 : Set (Welfare n)} {f : Welfare n → Rule n}
    (hpne : GuaranteesPNE 𝕎 f) {W : Welfare n} (hW : W ∈ 𝕎) :
    GuaranteesPNE {distributed (f W)} (fun _ => trimRule (f W)) := by
  intro m hm V hV A hA
  obtain ⟨a,ha,hbest⟩ := hpne m hm (fun _ => W) (fun _ => hW) A hA
  refine ⟨a,ha,?_⟩
  intro i b hb
  have h := hbest i b hb
  rw [utility_normalize V (fun _ => f W), utility_normalize V (fun _ => f W)]
  exact h

theorem localWeightSystems (n : ℕ) (hn : 1 < n) (𝕎 : Set (Welfare n))
    (f : Welfare n → Rule n) (hpne : GuaranteesPNE 𝕎 f) :
    ∃ Ω : Welfare n → Finset (Fin n) → WeightSystem n,
      ∀ W ∈ 𝕎, ∀ S : Finset (Fin n), ∀ i ∈ S,
        f W i S = ∑ T ∈ coalitions (distributed (f W)),
          mobius (distributed (f W)) T * gwsvBasis (Ω W T) T i S := by
  classical
  let w0 : WeightSystem n := ⟨1,fun _ => 0,fun _ => 1,fun _ => zero_lt_one⟩
  have hb (W : Welfare n) :
      IsBudgetBalanced (trimRule (f W)) (distributed (f W)) := by
    intro S
    exact Finset.sum_congr rfl (fun i hi => if_pos hi)
  have hzero (W : Welfare n) (i : Fin n) (S : Finset (Fin n)) (hi : i ∉ S) :
      trimRule (f W) i S = 0 := if_neg hi
  have hex : ∀ W ∈ 𝕎, ∀ T ∈ coalitions (distributed (f W)), ∃ ω : WeightSystem n,
      ∀ i S, basisRule (trimRule (f W)) (distributed (f W)) T i S = gwsvBasis ω T i S := by
    intro W hW
    exact lemma_8 n hn (distributed (f W)) (fun _ => trimRule (f W))
      (hb W) (localNormalize hpne hW) (hzero W)
  let Ω := fun W T => if h : W ∈ 𝕎 ∧ T ∈ coalitions (distributed (f W))
    then Classical.choose (hex W h.1 T h.2) else w0
  refine ⟨Ω, ?_⟩
  intro W hW S i hi
  have he := lemma_7 n hn (distributed (f W)) (fun _ => trimRule (f W))
    (hb W) (localNormalize hpne hW) (hzero W) S i hi
  change trimRule (f W) i S = _ at he
  rw [show trimRule (f W) i S = f W i S from if_pos hi] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro T hT
  have h := Classical.choose_spec (hex W hW T hT) i S
  have hdom : W ∈ 𝕎 ∧ T ∈ coalitions (distributed (f W)) := ⟨hW,hT⟩
  exact congrArg (_ * ·) (by simpa only [Ω, dif_pos hdom] using h)

open CostSharingPNE.Char

namespace CostSharingIndexedAux

variable {n : ℕ}

/-! ### Games with integer resource multiplicities and several welfare functions -/

/-- Players on resource `r` for a profile over an arbitrary resource type. -/
def pl {R : Type} [DecidableEq R] (a : Fin n → Finset R) (r : R) : Finset (Fin n) :=
  Finset.univ.filter (fun k => r ∈ a k)

lemma guarantees_mono {𝕎 𝕍 : Set (Welfare n)} (f : Welfare n → Rule n) (h : 𝕍 ⊆ 𝕎)
    (hpne : GuaranteesPNE 𝕎 f) : GuaranteesPNE 𝕍 f :=
  fun m hm W hW A hA => hpne m hm W (fun r => h (hW r)) A hA

/-- A game whose resource `r` carries the welfare function `Wl r ∈ 𝕎` and comes with `v r`
identical copies (the scaling coefficients `v_r` of Appendix A, p. 17). -/
lemma weighted_pne (𝕎 : Set (Welfare n)) (f : Welfare n → Rule n) (hpne : GuaranteesPNE 𝕎 f)
    (w0 : Welfare n) (hw0 : w0 ∈ 𝕎)
    {R : Type} [Fintype R] [DecidableEq R] (Wl : R → Welfare n) (hWl : ∀ r, Wl r ∈ 𝕎)
    (v : R → ℕ) (A : Fin n → Finset (Finset R)) (hA : ∀ k, (A k).Nonempty) :
    ∃ a : Fin n → Finset R, (∀ k, a k ∈ A k) ∧ ∀ k, ∀ b ∈ A k,
      ∑ r ∈ b, (v r : ℝ) * f (Wl r) k (pl (Function.update a k b) r) ≤
        ∑ r ∈ a k, (v r : ℝ) * f (Wl r) k (pl a r) := by
  classical
  let C := (Σ r : R, Fin (v r)) ⊕ Fin 2
  let m := Fintype.card C
  have hm : 1 < m := by
    show 1 < Fintype.card ((Σ r : R, Fin (v r)) ⊕ Fin 2)
    rw [Fintype.card_sum]; simp
  let e : C ≃ Fin m := Fintype.equivFin C
  let WC : C → Welfare n := fun c => Sum.elim (fun x => Wl x.1) (fun _ => w0) c
  let Wm : Fin m → Welfare n := fun x => WC (e.symm x)
  have hWm : ∀ x, Wm x ∈ 𝕎 := by
    intro x
    simp only [Wm, WC]
    cases e.symm x with
    | inl y => exact hWl y.1
    | inr _ => exact hw0
  let inlE : (Σ r : R, Fin (v r)) ↪ C := ⟨Sum.inl, Sum.inl_injective⟩
  let lift : Finset R → Finset (Fin m) := fun s =>
    ((s.sigma (fun r => (Finset.univ : Finset (Fin (v r))))).map inlE).map e.toEmbedding
  let A' : Fin n → Finset (Finset (Fin m)) := fun k => (A k).image lift
  have hA' : ∀ k, (A' k).Nonempty := fun k => (hA k).image _
  obtain ⟨a', ha', hN⟩ := hpne m hm Wm hWm A' hA'
  have hpre : ∀ k, ∃ s ∈ A k, lift s = a' k := by
    intro k
    have := ha' k
    simp only [A', Finset.mem_image] at this
    exact this
  choose a ha hla using hpre
  have ha'eq : a' = fun k => lift (a k) := by funext k; exact (hla k).symm
  have hU : ∀ (b : Fin n → Finset R) (k : Fin n),
      utility Wm f (fun k => lift (b k)) k =
        ∑ r ∈ b k, (v r : ℝ) * f (Wl r) k (pl b r) := by
    intro b k
    unfold utility
    have hpl : ∀ (r : R) (t : Fin (v r)),
        players (fun k => lift (b k)) (e (Sum.inl ⟨r, t⟩)) = pl b r := by
      intro r t; ext k'; simp [players, pl, lift, inlE]
    have hW : ∀ (r : R) (t : Fin (v r)), Wm (e (Sum.inl ⟨r, t⟩)) = Wl r := by
      intro r t; simp [Wm, WC]
    simp only [lift, Finset.sum_map]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r _
    have h2 : ∀ t : Fin (v r), f (Wm (e (Sum.inl ⟨r, t⟩))) k
        (players (fun k => lift (b k)) (e (Sum.inl ⟨r, t⟩))) = f (Wl r) k (pl b r) :=
      fun t => by rw [hpl r t, hW r t]
    refine (Finset.sum_congr rfl (fun t _ => h2 t)).trans ?_
    simp
  refine ⟨a, ha, fun k b hb => ?_⟩
  have hdev := hN k (lift b) (Finset.mem_image_of_mem lift hb)
  have hupd : Function.update a' k (lift b) = fun k' => lift (Function.update a k b k') := by
    funext k'
    by_cases hk : k' = k
    · subst hk; simp
    · rw [Function.update_of_ne hk, Function.update_of_ne hk, ha'eq]
  rw [hupd, ha'eq, hU, hU] at hdev
  simpa using hdev

/-! ### The 2 × 2 box game isolating basis shares (Counterexamples 4–5) -/

section Box

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (St : ι → Finset (Fin n)) (z : ι → ℤ) (i j : Fin n)

/-- Resources `r_1^t` (`b = 0`, top row) and `r_2^t` (`b = 1`, bottom row) for `t ∈ ι`. -/
abbrev Res (ι : Type) := ι × Fin 2

def vw (r : Res ι) : ℕ := (z r.1).natAbs

def topB (r : Res ι) : Bool := decide (r.2 = 0 ∧ i ∈ St r.1)
def botB (r : Res ι) : Bool := decide (r.2 = 1 ∧ i ∈ St r.1)
def lftB (r : Res ι) : Bool :=
  decide (j ∈ St r.1 ∧ ((r.2 = 0 ∧ z r.1 < 0) ∨ (r.2 = 1 ∧ 0 < z r.1)))
def rgtB (r : Res ι) : Bool :=
  decide (j ∈ St r.1 ∧ ((r.2 = 0 ∧ 0 < z r.1) ∨ (r.2 = 1 ∧ z r.1 < 0)))
def fixB (k : Fin n) (r : Res ι) : Bool := decide (k ∈ St r.1)

def act (B : Res ι → Bool) : Finset (Res ι) := Finset.univ.filter (fun r => B r = true)

lemma mem_act (B : Res ι → Bool) (r : Res ι) : r ∈ act B ↔ B r = true := by simp [act]

variable (Wl : ι → Welfare n) (f : Welfare n → Rule n)

/-- Share of player `p` on resource `r` when the other strategic player `q` is present iff
`X r`. -/
noncomputable def Fsh (p q : Fin n) (X : Res ι → Bool) (r : Res ι) : ℝ :=
  (vw z r : ℝ) * f (Wl r.1) p (if X r = true then St r.1 else (St r.1).erase q)

lemma sum_res (F : Res ι → ℝ) : ∑ r, F r = ∑ t, (F (t, 0) + F (t, 1)) := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]

lemma natAbs_neg' (x : ℤ) (hx : x < 0) : ((x.natAbs : ℕ) : ℝ) = -(x : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hx)]

lemma natAbs_pos' (x : ℤ) (hx : 0 < x) : ((x.natAbs : ℕ) : ℝ) = (x : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hx)]

lemma ite_erase (T : Finset (Fin n)) (x : Fin n) :
    (if x ∈ T then T else T.erase x) = T := by
  split_ifs with h
  · rfl
  · exact Finset.erase_eq_of_notMem h

lemma fin2_ne : ¬ ((0 : Fin 2) = 1) := by decide
lemma fin2_ne' : ¬ ((1 : Fin 2) = 0) := by decide

/-- `j`'s gain at `Top` from `L` to `R`. -/
lemma Kj_top (hjout : ∀ t, j ∉ St t → f (Wl t) j (St t) = f (Wl t) j ((St t).erase i)) :
    ∑ r ∈ act (rgtB St z j), Fsh St z Wl f j i (topB St i) r -
      ∑ r ∈ act (lftB St z j), Fsh St z Wl f j i (topB St i) r =
    ∑ t, (z t : ℝ) * (f (Wl t) j (St t) - f (Wl t) j ((St t).erase i)) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res]
  apply Finset.sum_congr rfl
  intro t _
  simp only [rgtB, lftB, topB, Fsh, vw, fin2_ne, fin2_ne', true_and, false_and,
    and_false, or_false, false_or, decide_eq_true_eq, ite_erase]
  by_cases hj : j ∈ St t
  · rcases lt_trichotomy (z t) 0 with hz | hz | hz
    · simp [hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
    · simp [hz]
    · simp [hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
  · simp [hj, hjout t hj]

/-- `j`'s gain at `Bottom` from `L` to `R`. -/
lemma Kj_bot (hjout : ∀ t, j ∉ St t → f (Wl t) j (St t) = f (Wl t) j ((St t).erase i)) :
    ∑ r ∈ act (rgtB St z j), Fsh St z Wl f j i (botB St i) r -
      ∑ r ∈ act (lftB St z j), Fsh St z Wl f j i (botB St i) r =
    -∑ t, (z t : ℝ) * (f (Wl t) j (St t) - f (Wl t) j ((St t).erase i)) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [rgtB, lftB, botB, Fsh, vw, fin2_ne, fin2_ne', true_and, false_and,
    and_false, or_false, false_or, decide_eq_true_eq, ite_erase]
  by_cases hj : j ∈ St t
  · rcases lt_trichotomy (z t) 0 with hz | hz | hz
    · simp [hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
    · simp [hz]
    · simp [hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
  · simp [hj, hjout t hj]

/-- `i`'s gain against `R` from `T` to `B`. -/
lemma Ki_rgt (hiout : ∀ t, i ∉ St t → f (Wl t) i (St t) = f (Wl t) i ((St t).erase j)) :
    ∑ r ∈ act (botB St i), Fsh St z Wl f i j (rgtB St z j) r -
      ∑ r ∈ act (topB St i), Fsh St z Wl f i j (rgtB St z j) r =
    -∑ t, (z t : ℝ) * (f (Wl t) i (St t) - f (Wl t) i ((St t).erase j)) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [rgtB, botB, topB, Fsh, vw, fin2_ne, fin2_ne', true_and, false_and,
    and_false, or_false, false_or, decide_eq_true_eq]
  by_cases hi : i ∈ St t
  · by_cases hj : j ∈ St t
    · rcases lt_trichotomy (z t) 0 with hz | hz | hz
      · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
      · simp [hz]
      · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
    · simp [hi, hj, Finset.erase_eq_of_notMem hj]
  · simp [hi, hiout t hi]

/-- `i`'s gain against `L` from `T` to `B`. -/
lemma Ki_lft (hiout : ∀ t, i ∉ St t → f (Wl t) i (St t) = f (Wl t) i ((St t).erase j)) :
    ∑ r ∈ act (botB St i), Fsh St z Wl f i j (lftB St z j) r -
      ∑ r ∈ act (topB St i), Fsh St z Wl f i j (lftB St z j) r =
    ∑ t, (z t : ℝ) * (f (Wl t) i (St t) - f (Wl t) i ((St t).erase j)) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res]
  apply Finset.sum_congr rfl
  intro t _
  simp only [lftB, botB, topB, Fsh, vw, fin2_ne, fin2_ne', true_and, false_and,
    and_false, or_false, false_or, decide_eq_true_eq]
  by_cases hi : i ∈ St t
  · by_cases hj : j ∈ St t
    · rcases lt_trichotomy (z t) 0 with hz | hz | hz
      · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
      · simp [hz]
      · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
    · simp [hi, hj, Finset.erase_eq_of_notMem hj]
  · simp [hi, hiout t hi]

end Box

open Classical in
/-- Players on a resource of the box game. -/
lemma pl_box {ι : Type} [Fintype ι] [DecidableEq ι] (St : ι → Finset (Fin n)) (i j : Fin n)
    (hij : i ≠ j) (b : Fin n → Finset (Res ι))
    (hbi : ∀ r ∈ b i, i ∈ St r.1) (hbj : ∀ r ∈ b j, j ∈ St r.1)
    (hfix : ∀ k, k ≠ i → k ≠ j → b k = act (fixB St k)) (r : Res ι) :
    pl b r = (St r.1).filter (fun k => (k = i → r ∈ b i) ∧ (k = j → r ∈ b j)) := by
  ext k
  simp only [pl, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hki : k = i
  · subst hki
    constructor
    · intro h; exact ⟨hbi r h, fun _ => h, fun h' => absurd h' hij⟩
    · rintro ⟨-, h, -⟩; exact h rfl
  by_cases hkj : k = j
  · subst hkj
    constructor
    · intro h; exact ⟨hbj r h, fun h' => absurd h' hki, fun _ => h⟩
    · rintro ⟨-, -, h⟩; exact h rfl
  rw [hfix k hki hkj, mem_act]
  simp [fixB, hki, hkj]

lemma pl_box_j {ι : Type} [Fintype ι] [DecidableEq ι] (St : ι → Finset (Fin n)) (i j : Fin n)
    (hij : i ≠ j) (b : Fin n → Finset (Res ι))
    (hbi : ∀ r ∈ b i, i ∈ St r.1) (hbj : ∀ r ∈ b j, j ∈ St r.1)
    (hfix : ∀ k, k ≠ i → k ≠ j → b k = act (fixB St k)) (r : Res ι) (hr : r ∈ b j) :
    pl b r = if r ∈ b i then St r.1 else (St r.1).erase i := by
  rw [pl_box St i j hij b hbi hbj hfix r]
  ext k
  by_cases h : r ∈ b i
  · simp only [h, if_true, Finset.mem_filter]
    constructor
    · exact fun h' => h'.1
    · intro hk; exact ⟨hk, fun _ => trivial, fun _ => hr⟩
  · simp only [h, if_false, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hk, h1, -⟩; exact ⟨h1, hk⟩
    · rintro ⟨hki, hk⟩; exact ⟨hk, fun h' => absurd h' hki, fun _ => hr⟩

lemma pl_box_i {ι : Type} [Fintype ι] [DecidableEq ι] (St : ι → Finset (Fin n)) (i j : Fin n)
    (hij : i ≠ j) (b : Fin n → Finset (Res ι))
    (hbi : ∀ r ∈ b i, i ∈ St r.1) (hbj : ∀ r ∈ b j, j ∈ St r.1)
    (hfix : ∀ k, k ≠ i → k ≠ j → b k = act (fixB St k)) (r : Res ι) (hr : r ∈ b i) :
    pl b r = if r ∈ b j then St r.1 else (St r.1).erase j := by
  rw [pl_box St i j hij b hbi hbj hfix r]
  ext k
  by_cases h : r ∈ b j
  · simp only [h, if_true, Finset.mem_filter]
    constructor
    · exact fun h' => h'.1
    · intro hk; exact ⟨hk, fun _ => hr, fun _ => trivial⟩
  · simp only [h, if_false, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hk, -, h1⟩; exact ⟨h1, hk⟩
    · rintro ⟨hkj, hk⟩; exact ⟨hk, fun _ => hr, fun h' => absurd h' hkj⟩

/-- The box game has a best-response cycle `TL → TR → BR → BL → TL` as soon as both
strategic players' gains are positive. -/
lemma box_cycle (𝕎 : Set (Welfare n)) (f : Welfare n → Rule n) (hpne : GuaranteesPNE 𝕎 f)
    (w0 : Welfare n) (hw0 : w0 ∈ 𝕎)
    {ι : Type} [Fintype ι] [DecidableEq ι] (St : ι → Finset (Fin n)) (z : ι → ℤ)
    (Wl : ι → Welfare n) (hWl : ∀ t, Wl t ∈ 𝕎) (i j : Fin n) (hij : i ≠ j)
    (hjout : ∀ t, j ∉ St t → f (Wl t) j (St t) = f (Wl t) j ((St t).erase i))
    (hiout : ∀ t, i ∉ St t → f (Wl t) i (St t) = f (Wl t) i ((St t).erase j))
    (hJ : 0 < ∑ t, (z t : ℝ) * (f (Wl t) j (St t) - f (Wl t) j ((St t).erase i)))
    (hI : 0 < -∑ t, (z t : ℝ) * (f (Wl t) i (St t) - f (Wl t) i ((St t).erase j))) :
    False := by
  classical
  let A : Fin n → Finset (Finset (Res ι)) := fun k =>
    if k = i then {act (topB St i), act (botB St i)}
    else if k = j then {act (lftB St z j), act (rgtB St z j)}
    else {act (fixB St k)}
  have hA : ∀ k, (A k).Nonempty := by
    intro k; simp only [A]; split_ifs <;> simp
  obtain ⟨a, ha, hN⟩ := weighted_pne 𝕎 f hpne w0 hw0 (fun r : Res ι => Wl r.1)
    (fun r => hWl r.1) (vw z) A hA
  have hai := ha i
  have haj := ha j
  simp only [A, if_true, if_neg (Ne.symm hij), Finset.mem_insert, Finset.mem_singleton] at hai haj
  have hfix : ∀ k, k ≠ i → k ≠ j → a k = act (fixB St k) := by
    intro k hki hkj
    have := ha k
    simp only [A, hki, hkj, if_false, Finset.mem_singleton] at this
    exact this
  have bT : ∀ r ∈ act (topB St i), i ∈ St r.1 := by
    intro r hr; rw [mem_act] at hr; simp only [topB, decide_eq_true_eq] at hr; exact hr.2
  have bB : ∀ r ∈ act (botB St i), i ∈ St r.1 := by
    intro r hr; rw [mem_act] at hr; simp only [botB, decide_eq_true_eq] at hr; exact hr.2
  have bL : ∀ r ∈ act (lftB St z j), j ∈ St r.1 := by
    intro r hr; rw [mem_act] at hr; simp only [lftB, decide_eq_true_eq] at hr; exact hr.1
  have bR : ∀ r ∈ act (rgtB St z j), j ∈ St r.1 := by
    intro r hr; rw [mem_act] at hr; simp only [rgtB, decide_eq_true_eq] at hr; exact hr.1
  have Uj : ∀ (b : Fin n → Finset (Res ι)) (X Y : Res ι → Bool),
      b i = act X → b j = act Y → (∀ r ∈ act X, i ∈ St r.1) → (∀ r ∈ act Y, j ∈ St r.1) →
      (∀ k, k ≠ i → k ≠ j → b k = act (fixB St k)) →
      ∑ r ∈ act Y, (vw z r : ℝ) * f (Wl r.1) j (pl b r) = ∑ r ∈ act Y, Fsh St z Wl f j i X r := by
    intro b X Y hbX hbY hX hY hbf
    apply Finset.sum_congr rfl
    intro r hr
    rw [pl_box_j St i j hij b (hbX ▸ hX) (hbY ▸ hY) hbf r (hbY ▸ hr)]
    simp only [Fsh, hbX, mem_act]
  have Ui : ∀ (b : Fin n → Finset (Res ι)) (X Y : Res ι → Bool),
      b i = act X → b j = act Y → (∀ r ∈ act X, i ∈ St r.1) → (∀ r ∈ act Y, j ∈ St r.1) →
      (∀ k, k ≠ i → k ≠ j → b k = act (fixB St k)) →
      ∑ r ∈ act X, (vw z r : ℝ) * f (Wl r.1) i (pl b r) = ∑ r ∈ act X, Fsh St z Wl f i j Y r := by
    intro b X Y hbX hbY hX hY hbf
    apply Finset.sum_congr rfl
    intro r hr
    rw [pl_box_i St i j hij b (hbX ▸ hX) (hbY ▸ hY) hbf r (hbX ▸ hr)]
    simp only [Fsh, hbY, mem_act]
  have updj : ∀ Y : Res ι → Bool, ∀ k, k ≠ i → k ≠ j →
      Function.update a j (act Y) k = act (fixB St k) := by
    intro Y k h1 h2; rw [Function.update_of_ne h2]; exact hfix k h1 h2
  have updi : ∀ X : Res ι → Bool, ∀ k, k ≠ i → k ≠ j →
      Function.update a i (act X) k = act (fixB St k) := by
    intro X k h1 h2; rw [Function.update_of_ne h1]; exact hfix k h1 h2
  have Kjt := Kj_top St z i j Wl f hjout
  have Kjb := Kj_bot St z i j Wl f hjout
  have Kir := Ki_rgt St z i j Wl f hiout
  have Kil := Ki_lft St z i j Wl f hiout
  have uji : Function.update a j (act (rgtB St z j)) i = a i := Function.update_of_ne hij _ _
  have uji' : Function.update a j (act (lftB St z j)) i = a i := Function.update_of_ne hij _ _
  have uij : Function.update a i (act (botB St i)) j = a j :=
    Function.update_of_ne (Ne.symm hij) _ _
  have uij' : Function.update a i (act (topB St i)) j = a j :=
    Function.update_of_ne (Ne.symm hij) _ _
  rcases hai with hai | hai <;> rcases haj with haj | haj
  · have hdev := hN j _ (show act (rgtB St z j) ∈ A j by simp [A, Ne.symm hij])
    rw [haj, Uj _ (topB St i) (rgtB St z j) (uji.trans hai) (by simp) bT bR (updj _),
      Uj a (topB St i) (lftB St z j) hai haj bT bL hfix] at hdev
    linarith
  · have hdev := hN i _ (show act (botB St i) ∈ A i by simp [A])
    rw [hai, Ui _ (botB St i) (rgtB St z j) (by simp) (uij.trans haj) bB bR (updi _),
      Ui a (topB St i) (rgtB St z j) hai haj bT bR hfix] at hdev
    linarith
  · have hdev := hN i _ (show act (topB St i) ∈ A i by simp [A])
    rw [hai, Ui _ (topB St i) (lftB St z j) (by simp) (uij'.trans haj) bT bL (updi _),
      Ui a (botB St i) (lftB St z j) hai haj bB bL hfix] at hdev
    linarith
  · have hdev := hN j _ (show act (lftB St z j) ∈ A j by simp [A, Ne.symm hij])
    rw [haj, Uj _ (botB St i) (lftB St z j) (uji'.trans hai) (by simp) bB bL (updj _),
      Uj a (botB St i) (rgtB St z j) hai haj bB bR hfix] at hdev
    linarith

lemma frac_bound (e y : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) : -|y| ≤ e * y ∧ e * y ≤ |y| := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; constructor <;> nlinarith
  · rw [abs_of_nonpos hy]; constructor <;> nlinarith

/-- If `x` and `y` are linearly independent in `ℝ²`, an integer vector `u` has `u·y > 0 > u·x`. -/
lemma int_sol (x1 x2 y1 y2 : ℝ) (hD : x1 * y2 - x2 * y1 ≠ 0) :
    ∃ u1 u2 : ℤ, 0 < (u1 : ℝ) * y1 + u2 * y2 ∧ (u1 : ℝ) * x1 + u2 * x2 < 0 := by
  set D := x1 * y2 - x2 * y1 with hDdef
  set a1 := -(x2 + y2) / D
  set a2 := (x1 + y1) / D
  have hax : a1 * x1 + a2 * x2 = -1 := by
    simp only [a1, a2]; field_simp; rw [hDdef]; ring
  have hay : a1 * y1 + a2 * y2 = 1 := by
    simp only [a1, a2]; field_simp; rw [hDdef]; ring
  obtain ⟨N, hN⟩ := exists_nat_gt (|x1| + |x2| + |y1| + |y2|)
  refine ⟨⌊(N : ℝ) * a1⌋, ⌊(N : ℝ) * a2⌋, ?_, ?_⟩
  · set e1 := (N : ℝ) * a1 - ⌊(N : ℝ) * a1⌋
    set e2 := (N : ℝ) * a2 - ⌊(N : ℝ) * a2⌋
    have h1 := frac_bound e1 y1 (by simp [e1, Int.floor_le]) (by
      simp only [e1]; linarith [Int.lt_floor_add_one ((N : ℝ) * a1)])
    have h2 := frac_bound e2 y2 (by simp [e2, Int.floor_le]) (by
      simp only [e2]; linarith [Int.lt_floor_add_one ((N : ℝ) * a2)])
    have : (⌊(N : ℝ) * a1⌋ : ℝ) * y1 + ⌊(N : ℝ) * a2⌋ * y2 = N * (a1 * y1 + a2 * y2) -
        (e1 * y1 + e2 * y2) := by simp only [e1, e2]; ring
    rw [this, hay]
    have := abs_nonneg x1; have := abs_nonneg x2
    linarith
  · set e1 := (N : ℝ) * a1 - ⌊(N : ℝ) * a1⌋
    set e2 := (N : ℝ) * a2 - ⌊(N : ℝ) * a2⌋
    have h1 := frac_bound e1 x1 (by simp [e1, Int.floor_le]) (by
      simp only [e1]; linarith [Int.lt_floor_add_one ((N : ℝ) * a1)])
    have h2 := frac_bound e2 x2 (by simp [e2, Int.floor_le]) (by
      simp only [e2]; linarith [Int.lt_floor_add_one ((N : ℝ) * a2)])
    have : (⌊(N : ℝ) * a1⌋ : ℝ) * x1 + ⌊(N : ℝ) * a2⌋ * x2 = N * (a1 * x1 + a2 * x2) -
        (e1 * x1 + e2 * x2) := by simp only [e1, e2]; ring
    rw [this, hax]
    have := abs_nonneg y1; have := abs_nonneg y2
    linarith

end CostSharingIndexedAux

open CostSharingIndexedAux in
theorem indexedConsistency (n : ℕ) (hn : 1 < n)
    (𝕎 : Set (Welfare n)) (f : Welfare n → Rule n) (hpne : GuaranteesPNE 𝕎 f)
    (L₁ L₂ : Welfare n) (hL₁ : L₁ ∈ 𝕎) (hL₂ : L₂ ∈ 𝕎)
    (W₁ W₂ : Welfare n)
    (hbb₁ : IsBudgetBalanced (f L₁) W₁) (hbb₂ : IsBudgetBalanced (f L₂) W₂)
    (h0₁ : ∀ i S, i ∉ S → f L₁ i S = 0) (h0₂ : ∀ i S, i ∉ S → f L₂ i S = 0) :
    ∀ i j : Fin n, ∀ T' ∈ coalitionsPair W₁ i j, ∀ T ∈ coalitionsPair W₂ i j,
      basisRule (f L₁) W₁ T' i T' * basisRule (f L₂) W₂ T j T =
        basisRule (f L₂) W₂ T i T * basisRule (f L₁) W₁ T' j T' := by
  intro i j T' hT' T hT
  unfold coalitionsPair at hT' hT
  rw [Finset.mem_filter] at hT' hT
  obtain ⟨hc1, hi1, hj1⟩ := hT'
  obtain ⟨hc2, hi2, hj2⟩ := hT
  by_cases hij : i = j
  · subst hij; ring
  by_contra hne
  have hq1 : mobius W₁ T' ≠ 0 := by
    unfold coalitions at hc1; exact (Finset.mem_filter.mp hc1).2.2
  have hq2 : mobius W₂ T ≠ 0 := by
    unfold coalitions at hc2; exact (Finset.mem_filter.mp hc2).2.2
  set B1 : Fin n → ℝ := fun x => basisRule (f L₁) W₁ T' x T' with hB1
  set B2 : Fin n → ℝ := fun x => basisRule (f L₂) W₂ T x T with hB2
  have hD : (mobius W₁ T' * B1 i) * (mobius W₂ T * B2 j) -
      (mobius W₂ T * B2 i) * (mobius W₁ T' * B1 j) ≠ 0 := by
    have : (mobius W₁ T' * B1 i) * (mobius W₂ T * B2 j) -
        (mobius W₂ T * B2 i) * (mobius W₁ T' * B1 j) =
        (mobius W₁ T' * mobius W₂ T) * (B1 i * B2 j - B2 i * B1 j) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hq1 hq2) (sub_ne_zero.mpr hne)
  obtain ⟨u1, u2, hy, hx⟩ := int_sol _ _ _ _ hD
  have hpConst (L V : Welfare n) (hL : L ∈ 𝕎) :
      GuaranteesPNE {V} (fun _ => f L) := by
    intro m hm W hW A hA
    obtain ⟨a,ha,hbest⟩ := hpne m hm (fun _ => L) (fun _ => hL) A hA
    exact ⟨a,ha,hbest⟩
  obtain ⟨c1, h49₁, h50₁⟩ := corollary_1 n hn W₁ (fun _ => f L₁)
    hbb₁ (hpConst L₁ W₁ hL₁) h0₁ T' hc1
  obtain ⟨c2, h49₂, h50₂⟩ := corollary_1 n hn W₂ (fun _ => f L₂)
    hbb₂ (hpConst L₂ W₂ hL₂) h0₂ T hc2
  let ι := {T'' // T'' ∈ coalitionsIn W₁ T'} ⊕ {T'' // T'' ∈ coalitionsIn W₂ T}
  let St : ι → Finset (Fin n) := Sum.elim (fun t => t.1) (fun t => t.1)
  let Wl : ι → Welfare n := Sum.elim (fun _ => L₁) (fun _ => L₂)
  let z : ι → ℤ := Sum.elim (fun t => u1 * c1 t.1) (fun t => u2 * c2 t.1)
  have hWl : ∀ t, Wl t ∈ 𝕎 := by
    intro t
    cases t with
    | inl _ => simpa [Wl] using hL₁
    | inr _ => simpa [Wl] using hL₂
  have key : ∀ x p : Fin n, x ∈ T' → x ∈ T → p ∈ T' → p ∈ T → p ≠ x →
      ∑ t, (z t : ℝ) * (f (Wl t) x (St t) - f (Wl t) x ((St t).erase p)) =
        u1 * (mobius W₁ T' * B1 x) + u2 * (mobius W₂ T * B2 x) := by
    intro x p hx1 hx2 hp1' hp2' hpx
    rw [Fintype.sum_sum_type]
    simp only [St, Wl, z, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_coe_sort (coalitionsIn W₁ T') (fun T'' => ((u1 * c1 T'' : ℤ) : ℝ) *
        (f L₁ x T'' - f L₁ x (T''.erase p))),
      Finset.sum_coe_sort (coalitionsIn W₂ T) (fun T'' => ((u2 * c2 T'' : ℤ) : ℝ) *
        (f L₂ x T'' - f L₂ x (T''.erase p)))]
    have e1 : ∑ T'' ∈ coalitionsIn W₁ T', ((u1 * c1 T'' : ℤ) : ℝ) *
        (f L₁ x T'' - f L₁ x (T''.erase p)) = u1 * (∑ T'' ∈ coalitionsIn W₁ T',
          (c1 T'' : ℝ) * f L₁ x T'' - ∑ T'' ∈ coalitionsIn W₁ T', (c1 T'' : ℝ) *
            f L₁ x (T''.erase p)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro _ _; push_cast; ring
    have e2 : ∑ T'' ∈ coalitionsIn W₂ T, ((u2 * c2 T'' : ℤ) : ℝ) *
        (f L₂ x T'' - f L₂ x (T''.erase p)) = u2 * (∑ T'' ∈ coalitionsIn W₂ T,
          (c2 T'' : ℝ) * f L₂ x T'' - ∑ T'' ∈ coalitionsIn W₂ T, (c2 T'' : ℝ) *
            f L₂ x (T''.erase p)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro _ _; push_cast; ring
    rw [e1, e2, ← h49₁ x hx1, ← h49₂ x hx2, ← (h50₁ x hx1 p hp1' hpx).2,
      ← (h50₁ x hx1 p hp1' hpx).1, ← (h50₂ x hx2 p hp2' hpx).2, ← (h50₂ x hx2 p hp2' hpx).1]
    simp only [B1, B2]
    ring
  have hjout : ∀ t, j ∉ St t → f (Wl t) j (St t) = f (Wl t) j ((St t).erase i) := by
    intro t ht
    cases t with
    | inl t =>
      simp only [St, Wl, Sum.elim_inl] at ht ⊢
      rw [h0₁ j _ ht, h0₁ j _ (fun h => ht (Finset.mem_of_mem_erase h))]
    | inr t =>
      simp only [St, Wl, Sum.elim_inr] at ht ⊢
      rw [h0₂ j _ ht, h0₂ j _ (fun h => ht (Finset.mem_of_mem_erase h))]
  have hiout : ∀ t, i ∉ St t → f (Wl t) i (St t) = f (Wl t) i ((St t).erase j) := by
    intro t ht
    cases t with
    | inl t =>
      simp only [St, Wl, Sum.elim_inl] at ht ⊢
      rw [h0₁ i _ ht, h0₁ i _ (fun h => ht (Finset.mem_of_mem_erase h))]
    | inr t =>
      simp only [St, Wl, Sum.elim_inr] at ht ⊢
      rw [h0₂ i _ ht, h0₂ i _ (fun h => ht (Finset.mem_of_mem_erase h))]
  apply box_cycle 𝕎 f hpne L₁ hL₁ St z Wl hWl i j hij hjout hiout
  · rw [key j i hj1 hj2 hi1 hi2 hij]
    linarith
  · rw [key i j hi1 hi2 hj1 hj2 (Ne.symm hij)]
    linarith

open CostSharingPNE.Char

private def trim {n : ℕ} (g : Rule n) : Rule n :=
  fun i S => if i ∈ S then g i S else 0

private lemma trim_guarantees {n : ℕ} {𝕎 : Set (Welfare n)} {f : Welfare n → Rule n}
    (hp : GuaranteesPNE 𝕎 f) : GuaranteesPNE 𝕎 (fun W => trim (f W)) := by
  intro m hm W hW A hA
  obtain ⟨a,ha,hb⟩ := hp m hm W hW A hA
  refine ⟨a,ha,?_⟩
  have hu (x : Fin n → Finset (Fin m)) (i : Fin n) :
      utility W (fun V => trim (f V)) x i = utility W f x i := by
    apply Finset.sum_congr rfl
    intro r hr
    exact if_pos (by simp [players,hr])
  intro i b hb'
  rw [hu,hu]
  exact hb i b hb'

theorem equalDistributed {n : ℕ} (hn : 1 < n) (𝕎 : Set (Welfare n))
    (f : Welfare n → Rule n) (hp : GuaranteesPNE 𝕎 f)
    (L₁ L₂ : Welfare n) (h₁ : L₁ ∈ 𝕎) (h₂ : L₂ ∈ 𝕎)
    (he : distributed (f L₁) = distributed (f L₂)) :
    trim (f L₁) = trim (f L₂) := by
  classical
  let g := fun L => trim (f L)
  let V := distributed (f L₁)
  have hg := trim_guarantees hp
  have hbb (L : Welfare n) : IsBudgetBalanced (g L) (distributed (f L)) :=
    fun S => Finset.sum_congr rfl (fun i hi => if_pos hi)
  have h0 (L : Welfare n) (i : Fin n) (S : Finset (Fin n)) (hi : i ∉ S) :
      g L i S = 0 := if_neg hi
  have hb₁ : IsBudgetBalanced (g L₁) V := hbb L₁
  have hb₂ : IsBudgetBalanced (g L₂) V := by
    change IsBudgetBalanced (g L₂) (distributed (f L₁))
    rw [he]
    exact hbb L₂
  have hs (L : Welfare n) (hL : L ∈ 𝕎) : GuaranteesPNE {V} (fun _ => g L) := by
    intro m hm W hW A hA
    exact hg m hm (fun _ => L) (fun _ => hL) A hA
  have hd := indexedConsistency n hn 𝕎 g hg L₁ L₂ h₁ h₂ V V hb₁ hb₂ (h0 L₁) (h0 L₂)
  funext i S
  change g L₁ i S = g L₂ i S
  by_cases hi : i ∈ S
  · rw [lemma_7 n hn V (fun _ => g L₁) hb₁ (hs L₁ h₁) (h0 L₁) S i hi,
        lemma_7 n hn V (fun _ => g L₂) hb₂ (hs L₂ h₂) (h0 L₂) S i hi]
    apply Finset.sum_congr rfl
    intro T hT
    obtain ⟨ω₁,hω₁⟩ := lemma_8 n hn V (fun _ => g L₁) hb₁ (hs L₁ h₁) (h0 L₁) T hT
    obtain ⟨ω₂,hω₂⟩ := lemma_8 n hn V (fun _ => g L₂) hb₂ (hs L₂ h₂) (h0 L₂) T hT
    have hsub (ω : WeightSystem n) : tbar ω T ⊆ T := by
      unfold tbar
      split <;> simp
    have hcoeff (j : Fin n) (hj : j ∈ T) :
        basisRule (g L₁) V T j T = basisRule (g L₂) V T j T := by
      have hx (k : Fin n) (hk : k ∈ T) :=
        hd j k T (Finset.mem_filter.mpr ⟨hT,hj,hk⟩)
          T (Finset.mem_filter.mpr ⟨hT,hj,hk⟩)
      have hh := Finset.sum_congr (s₁ := T) rfl (fun k hk => hx k hk)
      rw [← Finset.mul_sum, ← Finset.mul_sum] at hh
      have hsum₁ := lemma_5 n hn V (g L₁) hb₁ (h0 L₁) T hT T
      have hsum₂ := lemma_5 n hn V (g L₂) hb₂ (h0 L₂) T hT T
      rw [hsum₁,hsum₂] at hh
      simpa [unanimity] using hh
    by_cases hit : i ∈ T
    · rw [hω₁,hω₂]
      have hc := hcoeff i hit
      rw [hω₁,hω₂] at hc
      by_cases hTS : T ⊆ S
      · simpa only [gwsvBasis, hTS, and_true, Finset.Subset.refl] using congrArg (mobius V T * ·) hc
      · simp [gwsvBasis,hTS]
    · rw [hω₁,hω₂]
      simp [gwsvBasis,show i ∉ tbar ω₁ T from fun h => hit (hsub ω₁ h),
        show i ∉ tbar ω₂ T from fun h => hit (hsub ω₂ h)]
  · exact (h0 L₁ i S hi).trans (h0 L₂ i S hi).symm

open CostSharingPNE.Char

theorem solution (n : ℕ) (hn : 1 < n) (𝕎 : Set (Welfare n)) (h𝕎 : 𝕎.Nonempty)
    (f : Welfare n → Rule n) (hpne : GuaranteesPNE 𝕎 f) :
    ∃ ω : WeightSystem n, ∀ W ∈ 𝕎, ∀ S : Finset (Fin n), ∀ i ∈ S,
      f W i S = gwsv ω (distributed (f W)) i S := by
  classical
  let V : Set (Welfare n) := (fun W => distributed (f W)) '' 𝕎
  obtain ⟨L₀,hL₀⟩ := h𝕎
  have hex (v : Welfare n) (hv : v ∈ V) :
      ∃ L, L ∈ 𝕎 ∧ distributed (f L) = v := hv
  let pre := fun v => if hv : v ∈ V then Classical.choose (hex v hv) else L₀
  have hpre (v : Welfare n) (hv : v ∈ V) :
      pre v ∈ 𝕎 ∧ distributed (f (pre v)) = v := by
    simpa only [pre,dif_pos hv] using Classical.choose_spec (hex v hv)
  let g : Welfare n → Rule n := fun v i S => if i ∈ S then f (pre v) i S else 0
  have hbb : ∀ v ∈ V, IsBudgetBalanced (g v) v := by
    intro v hv S
    change (∑ i ∈ S, g v i S) = v S
    calc
      _ = distributed (f (pre v)) S := Finset.sum_congr rfl (fun i hi => if_pos hi)
      _ = v S := congrFun (hpre v hv).2 S
  have hgp : GuaranteesPNE V g := by
    intro m hm W hW A hA
    obtain ⟨a,ha,hb⟩ := hpne m hm (pre ∘ W) (fun r => (hpre _ (hW r)).1) A hA
    have hu (x : Fin n → Finset (Fin m)) (i : Fin n) :
        utility W g x i = utility (pre ∘ W) f x i := by
      apply Finset.sum_congr rfl
      intro r hr
      exact if_pos (by simp [players,hr])
    refine ⟨a,ha,?_⟩
    intro i b hB
    rw [hu,hu]
    exact hb i b hB
  have hdist (v : Welfare n) (hv : v ∈ V) : distributed (g v) = v :=
    funext (hbb v hv)
  obtain ⟨Ω,hΩ⟩ := localWeightSystems n hn V g hgp
  have hdec : ∀ v ∈ V, ∀ S : Finset (Fin n), ∀ i ∈ S,
      g v i S = ∑ T ∈ coalitions v, mobius v T * gwsvBasis (Ω v T) T i S := by
    intro v hv S i hi
    simpa only [hdist v hv] using hΩ v hv S i hi
  obtain ⟨ω,hω⟩ := lemma_13 n hn V g hbb hgp Ω hdec
  have hcommon : ∀ v ∈ V, ∀ T ∈ coalitions (distributed (g v)), ∀ i S,
      gwsvBasis (Ω v T) T i S = gwsvBasis ω T i S := by
    intro v hv T hT
    exact hω v hv T (by simpa only [hdist v hv] using hT)
  have hg := assembleNecessity V g Ω hΩ ω hcommon
  refine ⟨ω,?_⟩
  intro L hL S i hi
  let v := distributed (f L)
  have hv : v ∈ V := ⟨L,hL,rfl⟩
  have hr := equalDistributed hn 𝕎 f hpne (pre v) L (hpre v hv).1 hL (hpre v hv).2
  have he := congrFun (congrFun hr i) S
  change (if i ∈ S then f (pre v) i S else 0) = (if i ∈ S then f L i S else 0) at he
  simp only [if_pos hi] at he
  rw [← he]
  have h := hg v hv S i hi
  rw [hdist v hv] at h
  exact (if_pos hi : g v i S = f (pre v) i S).symm.trans h
