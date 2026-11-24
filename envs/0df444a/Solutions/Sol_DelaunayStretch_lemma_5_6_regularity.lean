-- Prove2me | solution 1 for DelaunayStretch.lemma_5_6_regularity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:27:12.619774+00:00
-- url     : https://prove2.me/submissions/d47e5589-6c6c-4fa0-80e2-a1b559183425

import Mathlib
import Definitions.Def_DelaunayStretch_FamilyPieces
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

open DelaunayStretch

namespace L56

def knotQ (j : ℕ) : ℚ := max 0 (min 1 (((j : ℚ) - 3) / 32))

def bpolyQ (k : ℕ) : ℕ → ℕ → ℚ → ℚ
  | 0, j, _ => if j = k + 3 then 1 else 0
  | p + 1, j, τ =>
      (τ - knotQ j) / (knotQ (j + p + 1) - knotQ j) * bpolyQ k p j τ +
        (knotQ (j + p + 2) - τ) / (knotQ (j + p + 2) - knotQ (j + 1)) * bpolyQ k p (j + 1) τ

def dpolyQ (k : ℕ) : ℕ → ℕ → ℚ → ℚ
  | 0, _, _ => 0
  | p + 1, j, τ =>
      1 / (knotQ (j + p + 1) - knotQ j) * bpolyQ k p j τ +
      (τ - knotQ j) / (knotQ (j + p + 1) - knotQ j) * dpolyQ k p j τ +
        (-1) / (knotQ (j + p + 2) - knotQ (j + 1)) * bpolyQ k p (j + 1) τ +
        (knotQ (j + p + 2) - τ) / (knotQ (j + p + 2) - knotQ (j + 1)) * dpolyQ k p (j + 1) τ

theorem checkB : ∀ k < 31, ∀ l < 35,
    bpolyQ k 3 l (((k:ℚ) + 1) / 32) = bpolyQ (k + 1) 3 l (((k:ℚ) + 1) / 32) := by
  decide +kernel

theorem checkD : ∀ k < 31, ∀ l < 35,
    dpolyQ k 3 l (((k:ℚ) + 1) / 32) = dpolyQ (k + 1) 3 l (((k:ℚ) + 1) / 32) := by
  decide +kernel

theorem check0 : ∀ l < 35, bpolyQ 0 3 l 0 = if l = 0 then 1 else 0 := by
  decide +kernel

end L56



namespace L56

noncomputable def bpolyR (k : ℕ) : ℕ → ℕ → ℝ → ℝ
  | 0, j, _ => if j = k + 3 then 1 else 0
  | p + 1, j, τ =>
      (τ - knotQ j) / ((knotQ (j + p + 1) : ℝ) - knotQ j) * bpolyR k p j τ +
        ((knotQ (j + p + 2) : ℝ) - τ) / ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1)) *
          bpolyR k p (j + 1) τ

noncomputable def dpolyR (k : ℕ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | p + 1, j, τ =>
      1 / ((knotQ (j + p + 1) : ℝ) - knotQ j) * bpolyR k p j τ +
      (τ - knotQ j) / ((knotQ (j + p + 1) : ℝ) - knotQ j) * dpolyR k p j τ +
        (-1) / ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1)) * bpolyR k p (j + 1) τ +
        ((knotQ (j + p + 2) : ℝ) - τ) / ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1)) *
          dpolyR k p (j + 1) τ

theorem splineKnot_eq (j : ℕ) : splineKnot j = (knotQ j : ℝ) := by
  simp [splineKnot, knotQ]

theorem bpolyR_cast (k p j : ℕ) (q : ℚ) : bpolyR k p j (q : ℝ) = (bpolyQ k p j q : ℝ) := by
  induction p generalizing j with
  | zero => simp [bpolyR, bpolyQ]; split_ifs <;> simp
  | succ p ih => simp [bpolyR, bpolyQ, ih]

theorem dpolyR_cast (k p j : ℕ) (q : ℚ) : dpolyR k p j (q : ℝ) = (dpolyQ k p j q : ℝ) := by
  induction p generalizing j with
  | zero => simp [dpolyR, dpolyQ]
  | succ p ih => simp [dpolyR, dpolyQ, ih, bpolyR_cast]

theorem bpolyR_contDiff (k p j : ℕ) : ContDiff ℝ 1 (bpolyR k p j) := by
  induction p generalizing j with
  | zero => exact contDiff_const
  | succ p ih =>
    have h1 := ih j
    have h2 := ih (j + 1)
    show ContDiff ℝ 1 (fun τ => (τ - knotQ j) / ((knotQ (j + p + 1) : ℝ) - knotQ j) * bpolyR k p j τ +
        ((knotQ (j + p + 2) : ℝ) - τ) / ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1)) *
          bpolyR k p (j + 1) τ)
    fun_prop

theorem bpolyR_hasDerivAt (k p j : ℕ) (τ : ℝ) :
    HasDerivAt (bpolyR k p j) (dpolyR k p j τ) τ := by
  induction p generalizing j with
  | zero => exact hasDerivAt_const _ _
  | succ p ih =>
    have h1 := ((((hasDerivAt_id τ).sub_const (knotQ j : ℝ)).div_const
      ((knotQ (j + p + 1) : ℝ) - knotQ j)).mul (ih j)).add
      ((((hasDerivAt_id τ).const_sub (knotQ (j + p + 2) : ℝ)).div_const
      ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1))).mul (ih (j + 1)))
    have h2 : HasDerivAt (bpolyR k (p+1) j) _ τ := h1.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by simp [bpolyR])
    exact h2.congr_deriv (by simp only [dpolyR, id]; ring)

theorem bsplineDeg0Ext_eq (k : ℕ) (hk : k ≤ 31) (τ : ℝ) (h1 : k = 0 ∨ (k : ℝ) / 32 ≤ τ)
    (h2 : τ < ((k : ℝ) + 1) / 32) (j : ℕ) :
    bsplineDeg0Ext j τ = if j = k + 3 then 1 else 0 := by
  unfold bsplineDeg0Ext
  by_cases hτ : τ < 0
  · have : k = 0 := by
      rcases h1 with h | h
      · exact h
      · exfalso; have : (0:ℝ) ≤ k / 32 := by positivity
        linarith
    subst this; simp [hτ]
  · simp only [hτ, if_false]
    push Not at hτ
    have hk' : (k : ℝ) / 32 ≤ τ := by
      rcases h1 with h | h
      · subst h; simpa using hτ
      · exact h
    have hk32 : (k : ℝ) + 1 ≤ 32 := by exact_mod_cast (by omega : k + 1 ≤ 32)
    unfold bsplineDeg0
    have hne1 : τ ≠ 1 := by intro h; rw [h] at h2; linarith
    by_cases hj : j = k + 3
    · subst hj
      simp only [if_true]
      rw [if_pos]
      left
      unfold splineKnot
      push_cast
      constructor
      · have : ((k:ℝ) + 3 - 3) / 32 = k / 32 := by ring
        rw [this]
        apply max_le hτ
        exact le_trans (min_le_right _ _) hk'
      · have : ((k:ℝ) + 3 + 1 - 3) / 32 = (k + 1) / 32 := by ring
        rw [this]
        have : min 1 (((k:ℝ) + 1) / 32) = (k + 1) / 32 := by
          apply min_eq_right; rw [div_le_one (by norm_num)]; exact hk32
        rw [this]
        exact lt_of_lt_of_le h2 (le_max_right _ _)
    · simp only [hj, if_false]
      rw [if_neg]
      rintro (⟨ha, hb⟩ | ⟨rfl, h⟩)
      · rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
        · -- j < k + 3: knot (j+1) ≤ τ
          have hjr : (j : ℝ) + 1 ≤ k + 3 := by exact_mod_cast hlt
          unfold splineKnot at hb
          push_cast at hb
          have : max 0 (min 1 (((j:ℝ) + 1 - 3) / 32)) ≤ τ := by
            apply max_le hτ
            refine le_trans (min_le_right _ _) (le_trans ?_ hk')
            apply div_le_div_of_nonneg_right _ (by norm_num); linarith
          linarith
        · have hjr : (k : ℝ) + 4 ≤ j := by exact_mod_cast hgt
          unfold splineKnot at ha
          have : τ < max 0 (min 1 (((j:ℝ) - 3) / 32)) := by
            refine lt_of_lt_of_le ?_ (le_max_right _ _)
            apply lt_min
            · linarith
            · refine lt_of_lt_of_le h2 ?_
              apply div_le_div_of_nonneg_right _ (by norm_num); linarith
          linarith
      · exact hne1 h

/-- the interval `I_k` -/
def InI (k : ℕ) (τ : ℝ) : Prop := (k = 0 ∨ (k : ℝ) / 32 ≤ τ) ∧ τ < ((k : ℝ) + 1) / 32

theorem basisExt_eq (k : ℕ) (hk : k ≤ 31) (τ : ℝ) (hτ : InI k τ) (p j : ℕ) :
    bsplineBasisExt p j τ = bpolyR k p j τ := by
  induction p generalizing j with
  | zero => simp only [bsplineBasisExt, bpolyR]; exact bsplineDeg0Ext_eq k hk τ hτ.1 hτ.2 j
  | succ p ih =>
    simp only [bsplineBasisExt, bpolyR, splineKnot_eq, ih]

theorem bsplineExt_eq (k : ℕ) (hk : k ≤ 31) (τ : ℝ) (hτ : InI k τ) (l : ℕ) :
    bsplineExt l τ = bpolyR k 3 l τ := basisExt_eq k hk τ hτ 3 l

/-- gluing two `C¹` functions with matching value and derivative -/
theorem glue_contDiff (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (c : ℝ)
    (h0 : u c = v c) (h1 : deriv u c = deriv v c) :
    ContDiff ℝ 1 (fun x => if x < c then u x else v x) := by
  set g := fun x => if x < c then u x else v x with hg
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  set g' := fun x => if c ≤ x then deriv v x else deriv u x with hg'
  have hder : ∀ x, HasDerivAt g (g' x) x := by
    intro x
    rcases lt_trichotomy x c with hx | hx | hx
    · have : g =ᶠ[nhds x] u := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        simp [hg, show y < c from hy]
      have h2 : g' x = deriv u x := by simp [hg', not_le.mpr hx]
      rw [h2]
      exact (hud x).hasDerivAt.congr_of_eventuallyEq this
    · subst hx
      have h2 : g' x = deriv v x := by simp [hg']
      rw [h2]
      have hl : HasDerivWithinAt g (deriv v x) (Set.Iic x) x := by
        rw [← h1]
        apply (hud x).hasDerivAt.hasDerivWithinAt.congr
        · intro y hy
          rcases (Set.mem_Iic.mp hy).lt_or_eq with h | h
          · simp [hg, h]
          · subst h; simp [hg, h0]
        · simp [hg, h0]
      have hr : HasDerivWithinAt g (deriv v x) (Set.Ici x) x := by
        apply (hvd x).hasDerivAt.hasDerivWithinAt.congr
        · intro y hy
          simp [hg, not_lt.mpr (Set.mem_Ici.mp hy)]
        · simp [hg]
      have := hl.union hr
      rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
      exact this
    · have : g =ᶠ[nhds x] v := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        simp [hg, not_lt.mpr (le_of_lt (show c < y from hy))]
      have h2 : g' x = deriv v x := by simp [hg', le_of_lt hx]
      rw [h2]
      exact (hvd x).hasDerivAt.congr_of_eventuallyEq this
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hder x).differentiableAt, ?_⟩
  have : deriv g = g' := funext fun x => (hder x).deriv
  rw [this]
  exact Continuous.if_le (hv.continuous_deriv le_rfl) (hu.continuous_deriv le_rfl)
    continuous_const continuous_id (fun x hx => by rw [← hx, h1])

end L56



namespace L56

theorem knot_value (m l : ℕ) (hm : m < 31) (hl : l < 35) :
    bpolyR m 3 l (((m : ℝ) + 1) / 32) = bpolyR (m + 1) 3 l (((m : ℝ) + 1) / 32) := by
  have h := checkB m hm l hl
  have e : (((m : ℝ) + 1) / 32) = ((((m : ℚ) + 1) / 32 : ℚ) : ℝ) := by push_cast; ring
  rw [e, bpolyR_cast, bpolyR_cast, h]

theorem knot_deriv (m l : ℕ) (hm : m < 31) (hl : l < 35) :
    deriv (bpolyR m 3 l) (((m : ℝ) + 1) / 32) =
      deriv (bpolyR (m + 1) 3 l) (((m : ℝ) + 1) / 32) := by
  have h := checkD m hm l hl
  rw [(bpolyR_hasDerivAt _ _ _ _).deriv, (bpolyR_hasDerivAt _ _ _ _).deriv]
  have e : (((m : ℝ) + 1) / 32) = ((((m : ℚ) + 1) / 32 : ℚ) : ℝ) := by push_cast; ring
  rw [e, dpolyR_cast, dpolyR_cast, h]

theorem bsplineExt_contDiffAt (l : ℕ) (hl : l < 35) (x : ℝ) (hx : x < 1) :
    ContDiffAt ℝ 1 (bsplineExt l) x := by
  by_cases h0 : x < 1 / 32
  · have : bsplineExt l =ᶠ[nhds x] bpolyR 0 3 l := by
      filter_upwards [Iio_mem_nhds h0] with y hy
      exact bsplineExt_eq 0 (by norm_num) y ⟨Or.inl rfl, by simpa using hy⟩ l
    exact ((bpolyR_contDiff 0 3 l).contDiffAt).congr_of_eventuallyEq this
  push Not at h0
  obtain ⟨n, hn1, hn2, hn3⟩ : ∃ n : ℕ, (n : ℝ) ≤ 32 * x ∧ 32 * x < n + 1 ∧ 1 ≤ n :=
    ⟨⌊32 * x⌋₊, Nat.floor_le (by linarith), Nat.lt_floor_add_one _,
      Nat.le_floor (by push_cast; linarith)⟩
  have hn4 : n ≤ 31 := by
    have : (n : ℝ) < 32 := by linarith
    exact_mod_cast (show (n : ℝ) ≤ 31 by
      have : n < 32 := by exact_mod_cast this
      exact_mod_cast (by omega : n ≤ 31))
  by_cases he : (n : ℝ) = 32 * x
  · -- knot case, n = m + 1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m < 31 := by omega
    have hxe : x = ((m : ℝ) + 1) / 32 := by push_cast at he; linarith
    have hlo : (m : ℝ) / 32 < x := by rw [hxe]; linarith
    have hhi : x < ((m : ℝ) + 2) / 32 := by rw [hxe]; linarith
    set c := ((m : ℝ) + 1) / 32
    have hg := glue_contDiff (bpolyR m 3 l) (bpolyR (m + 1) 3 l) (bpolyR_contDiff _ _ _)
      (bpolyR_contDiff _ _ _) c (knot_value m l hm hl) (knot_deriv m l hm hl)
    refine hg.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    by_cases hyc : y < c
    · simp only [hyc, if_true]
      exact bsplineExt_eq m (by omega) y ⟨Or.inr hy1.le, hyc⟩ l
    · simp only [hyc, if_false]
      push Not at hyc
      refine bsplineExt_eq (m + 1) (by omega) y ⟨Or.inr ?_, ?_⟩ l
      · push_cast; exact hyc
      · push_cast; linarith
  · have hlo : (n : ℝ) / 32 < x := by
      have : (n : ℝ) < 32 * x := lt_of_le_of_ne hn1 he
      linarith
    have hhi : x < ((n : ℝ) + 1) / 32 := by linarith
    have : bsplineExt l =ᶠ[nhds x] bpolyR n 3 l := by
      filter_upwards [Ioo_mem_nhds hlo hhi] with y hy
      exact bsplineExt_eq n hn4 y ⟨Or.inr hy.1.le, hy.2⟩ l
    exact ((bpolyR_contDiff n 3 l).contDiffAt).congr_of_eventuallyEq this

theorem basis_eq_ext (τ : ℝ) (hτ : 0 ≤ τ) (p j : ℕ) :
    bsplineBasis p j τ = bsplineBasisExt p j τ := by
  induction p generalizing j with
  | zero => simp [bsplineBasis, bsplineBasisExt, bsplineDeg0Ext, not_lt.mpr hτ]
  | succ p ih => simp only [bsplineBasis, bsplineBasisExt, ih]

theorem bspline_eq_ext (l : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) : bspline l τ = bsplineExt l τ :=
  basis_eq_ext τ hτ 3 l

theorem bspline_zero (l : ℕ) (hl : l < 35) : bspline l 0 = if l = 0 then 1 else 0 := by
  rw [bspline_eq_ext l 0 le_rfl, bsplineExt_eq 0 (by norm_num) 0 ⟨Or.inl rfl, by norm_num⟩ l]
  have h := check0 l hl
  have e : (0 : ℝ) = ((0 : ℚ) : ℝ) := by simp
  rw [e, bpolyR_cast, h]
  split_ifs <;> simp

end L56



namespace L56

section
variable (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (Bc Dc : Fin 35 → ℚ)

/-! ### Symmetry at `γ = 0` -/

theorem familyV_zero (a b : ℝ) : familyV V 0 a b =
    ∑ i : Fin 12, ∑ j : Fin 12, (V i j 0 : ℝ) * bernstein 11 i a * bernstein 11 j b := by
  unfold familyV
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (0 : Fin 35)]
  · simp [bspline_zero]
  · intro l _ hl
    have : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
    simp [bspline_zero l l.isLt, this]
  · simp

theorem familyR_zero (a b : ℝ) : familyR R 0 a b =
    ∑ i : Fin 6, ∑ j : Fin 6, (R i j 0 : ℝ) * bernstein 5 i a * bernstein 5 j b := by
  unfold familyR
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (0 : Fin 35)]
  · simp [bspline_zero]
  · intro l _ hl
    have : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
    simp [bspline_zero l l.isLt, this]
  · simp

theorem familySpline_zero (c : Fin 35 → ℚ) : familySpline c 0 = c 0 := by
  unfold familySpline
  rw [Finset.sum_eq_single (0 : Fin 35)]
  · simp [bspline_zero]
  · intro l _ hl
    have : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
    simp [bspline_zero l l.isLt, this]
  · simp

theorem familyV_swap (hc : FamilyCoeffConditions V R Bc Dc) (a b : ℝ) :
    familyV V 0 b a = familyV V 0 a b := by
  rw [familyV_zero, familyV_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hc.2.2.2.1 j i]; ring

theorem familyR_swap (hc : FamilyCoeffConditions V R Bc Dc) (a b : ℝ) :
    familyR R 0 b a = -familyR R 0 a b := by
  rw [familyR_zero, familyR_zero, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc.2.2.2.2.1 j i]; push_cast; ring

theorem familyV_corner (hc : FamilyCoeffConditions V R Bc Dc) : familyV V 0 0 1 = 0 := by
  rw [familyV_zero]
  have h1 := hc.1 0 ((11 : Fin 12)) 0
  have h2 := hc.2.2.2.1 ((11 : Fin 12)) 0
  have hr0 : Fin.rev (0 : Fin 12) = (11 : Fin 12) := rfl
  have hr1 : Fin.rev ((11 : Fin 12)) = (0 : Fin 12) := rfl
  rw [hr0, hr1] at h1
  have hz : V 0 ((11 : Fin 12)) 0 = 0 := by linarith
  rw [Finset.sum_eq_single (0 : Fin 12)]
  · rw [Finset.sum_eq_single ((11 : Fin 12))]
    · simp [hz]
    · intro j _ hj
      have : (j : ℕ) ≠ 11 := fun h => hj (Fin.ext h)
      have : 11 - (j : ℕ) ≠ 0 := by have := j.isLt; omega
      simp [DelaunayStretch.bernstein, this]
    · simp
  · intro i _ hi
    have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [DelaunayStretch.bernstein, this]
  · simp

theorem clip_neg (x : ℝ) : clip 1 (-x) = -clip 1 x := by
  unfold clip
  rcases le_total x (-1) with h | h <;> rcases le_total x 1 with h' | h' <;>
    simp [max_def, min_def] <;> split_ifs <;> linarith

theorem familyHPos_zero_sym (hc : FamilyCoeffConditions V R Bc Dc) (φ θ ψ : ℝ) :
    familyHPos V R Bc Dc 0 (-φ) θ (-ψ) = familyHPos V R Bc Dc 0 φ θ ψ := by
  simp only [familyHPos]
  have e1 : (θ - -φ + 0) / (Real.pi + 2 * 0) = (θ + φ - 0) / (Real.pi - 2 * 0) := by ring
  have e2 : (θ + -φ - 0) / (Real.pi - 2 * 0) = (θ - φ + 0) / (Real.pi + 2 * 0) := by ring
  rw [e1, e2, neg_div, clip_neg, familyV_swap V R Bc Dc hc, familyR_swap V R Bc Dc hc,
    familyV_corner V R Bc Dc hc, familySpline_zero, familySpline_zero, hc.2.2.2.2.2.1,
    hc.2.2.2.2.2.2]
  push_cast
  ring

theorem familyH_reflect (hc : FamilyCoeffConditions V R Bc Dc) (z : R4) :
    familyH V R Bc Dc (reflect1 z) = familyH V R Bc Dc z := by
  unfold familyH reflect1
  simp only [neg_neg]
  rcases lt_trichotomy z.1 0 with h | h | h
  · have h1 : 0 ≤ -z.1 := by linarith
    simp [h1, not_le.mpr h]
  · rw [h]
    simp only [neg_zero, le_refl, if_true]
    exact familyHPos_zero_sym V R Bc Dc hc _ _ _
  · have h1 : ¬ (0 ≤ -z.1) := by linarith
    simp [h1, h.le]

end

end L56



namespace L56

section
variable (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (Bc Dc : Fin 35 → ℚ)

noncomputable def Hhat4 (w : R4) : ℝ := familyHhat V R Bc Dc w.1 w.2.1 w.2.2.1 w.2.2.2

theorem spline_comp_contDiffAt (l : Fin 35) (w : R4) (hw : w.1 < Real.pi / 2) :
    ContDiffAt ℝ 1 (fun w : R4 => bsplineExt l (2 * w.1 / Real.pi)) w := by
  have h : 2 * w.1 / Real.pi < 1 := by
    rw [div_lt_one Real.pi_pos]; linarith
  have h2 : ContDiffAt ℝ 1 (fun w : R4 => 2 * w.1 / Real.pi) w := by fun_prop
  exact (bsplineExt_contDiffAt l l.isLt _ h).comp w h2

theorem Hhat4_contDiffAt (w : R4) (hw : w.1 < Real.pi / 2) :
    ContDiffAt ℝ 1 (Hhat4 V R Bc Dc) w := by
  have hs := fun l => spline_comp_contDiffAt l w hw
  unfold Hhat4 familyHhat familyVExt familyRExt familySplineExt DelaunayStretch.bernstein
  fun_prop

def Vset : Set R4 := {z | |z.1| < Real.pi / 2}

theorem isOpen_Vset : IsOpen Vset :=
  isOpen_lt (continuous_abs.comp continuous_fst) continuous_const

theorem omega_sub_Vset : OmegaTimesR ⊆ Vset := by
  intro z hz
  simp only [OmegaTimesR, OmegaSet, Set.mem_setOf_eq] at hz
  show |z.1| < Real.pi / 2
  obtain ⟨h1, h2⟩ := hz
  have : 2 * |z.1| ≤ |z.1 - z.2.1| + |z.1 + z.2.1| := by
    have := abs_add_le (z.1 - z.2.1) (z.1 + z.2.1)
    rw [show z.1 - z.2.1 + (z.1 + z.2.1) = 2 * z.1 by ring, abs_mul] at this
    simpa using this
  linarith

theorem kpos (γ : ℝ) : 0 < Real.pi / 2 - Real.cos γ := by
  have := Real.cos_le_one γ
  have := Real.pi_gt_three
  linarith

noncomputable def mC (z : R4) : R4 := (z.1, posA z, posB z, balanceXi z)

noncomputable def mO (s : ℝ) (z : R4) : R4 := (z.1, posA z, posB z, s)

theorem posA_contDiffAt (z : R4) (hz : z ∈ Vset) : ContDiffAt ℝ 1 posA z := by
  have : Real.pi + 2 * z.1 ≠ 0 := by
    have := (abs_lt.mp (show |z.1| < Real.pi / 2 from hz)).1; linarith
  unfold posA
  exact ContDiffAt.div (by fun_prop) (by fun_prop) this

theorem posB_contDiffAt (z : R4) (hz : z ∈ Vset) : ContDiffAt ℝ 1 posB z := by
  have : Real.pi - 2 * z.1 ≠ 0 := by
    have := (abs_lt.mp (show |z.1| < Real.pi / 2 from hz)).2; linarith
  unfold posB
  exact ContDiffAt.div (by fun_prop) (by fun_prop) this

theorem balanceXi_contDiffAt (z : R4) : ContDiffAt ℝ 1 balanceXi z := by
  unfold balanceXi
  exact ContDiffAt.div (by fun_prop) (by fun_prop) (kpos z.1).ne'

theorem balanceXi_continuous : Continuous balanceXi := by
  unfold balanceXi
  exact Continuous.div (by fun_prop) (by fun_prop) (fun z => (kpos z.1).ne')

theorem mC_contDiffAt (z : R4) (hz : z ∈ Vset) : ContDiffAt ℝ 1 mC z := by
  have h1 := posA_contDiffAt z hz
  have h2 := posB_contDiffAt z hz
  have h3 := balanceXi_contDiffAt z
  unfold mC
  fun_prop

theorem mO_contDiffAt (s : ℝ) (z : R4) (hz : z ∈ Vset) : ContDiffAt ℝ 1 (mO s) z := by
  have h1 := posA_contDiffAt z hz
  have h2 := posB_contDiffAt z hz
  unfold mO
  fun_prop

theorem lt_of_Vset (z : R4) (hz : z ∈ Vset) : z.1 < Real.pi / 2 :=
  (abs_lt.mp (show |z.1| < Real.pi / 2 from hz)).2

theorem pieceHc_contDiffAt (z : R4) (hz : z ∈ Vset) :
    ContDiffAt ℝ 1 (pieceHc V R Bc Dc) z := by
  have := (Hhat4_contDiffAt V R Bc Dc (mC z) (lt_of_Vset z hz)).comp z (mC_contDiffAt z hz)
  exact this

theorem pieceHout_contDiffAt (s : ℝ) (z : R4) (hz : z ∈ Vset) :
    ContDiffAt ℝ 1 (pieceHout V R Bc Dc s) z := by
  have := (Hhat4_contDiffAt V R Bc Dc (mO s z) (lt_of_Vset z hz)).comp z (mO_contDiffAt s z hz)
  exact this

/-! ### the reflection -/

def reflLin : R4 →ₗ[ℝ] R4 where
  toFun := reflect1
  map_add' x y := by
    simp only [reflect1, Prod.fst_add, Prod.snd_add, neg_add, Prod.mk_add_mk]
  map_smul' c x := by
    simp only [reflect1, Prod.smul_fst, Prod.smul_snd, smul_neg, RingHom.id_apply,
      Prod.smul_mk]

noncomputable def reflL : R4 →L[ℝ] R4 := LinearMap.toContinuousLinearMap reflLin

theorem reflL_apply (z : R4) : reflL z = reflect1 z := rfl

theorem reflect1_contDiff : ContDiff ℝ 1 reflect1 := by
  have : reflect1 = (reflL : R4 → R4) := funext fun z => rfl
  rw [this]; exact reflL.contDiff

theorem reflect1_reflect1 (z : R4) : reflect1 (reflect1 z) = z := by
  simp [reflect1]

theorem reflect1_mem_Vset (z : R4) : reflect1 z ∈ Vset ↔ z ∈ Vset := by
  simp [Vset, reflect1, abs_neg]

theorem reflect1_mem_omega (z : R4) : reflect1 z ∈ OmegaTimesR ↔ z ∈ OmegaTimesR := by
  simp only [OmegaTimesR, OmegaSet, Set.mem_setOf_eq, reflect1]
  rw [show -z.1 - -z.2.1 = -(z.1 - z.2.1) by ring, show -z.1 + -z.2.1 = -(z.1 + z.2.1) by ring,
    abs_neg, abs_neg]

theorem gradient4_reflect (F : R4 → ℝ) (z : R4) (hF : DifferentiableAt ℝ F (reflect1 z)) :
    gradient4 (F ∘ reflect1) z =
      (-(gradient4 F (reflect1 z)).1, -(gradient4 F (reflect1 z)).2.1,
        (gradient4 F (reflect1 z)).2.2.1, -(gradient4 F (reflect1 z)).2.2.2) := by
  have hR : HasFDerivAt reflect1 reflL z := reflL.hasFDerivAt
  have h := hF.hasFDerivAt.comp z hR
  unfold gradient4
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, reflL_apply, reflect1, neg_zero]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only
  · rw [show ((-1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)) = -((1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)) by simp,
      map_neg]
  · rw [show ((0 : ℝ), (-1 : ℝ), (0 : ℝ), (0 : ℝ)) = -((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ)) by simp,
      map_neg]
  · rw [show ((0 : ℝ), (0 : ℝ), (0 : ℝ), (-1 : ℝ)) = -((0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ)) by simp,
      map_neg]

theorem pencil_reflect (U : ℝ) (H : R4 → ℝ) (g z : R4) (hH : H (reflect1 z) = H z) :
    pencilResidual U H (-g.1, -g.2.1, g.2.2.1, -g.2.2.2) (reflect1 z) = pencilResidual U H g z := by
  unfold pencilResidual
  rw [hH]
  simp only [pencilA, reflect1, Real.sin_neg, Real.cos_neg]
  ring

end

end L56



namespace L56

/-! ### Lipschitz gluing -/

theorem glue_mixed (f : R4 → ℝ) (z0 : R4) (r K1 K2 : ℝ) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (h1 : ∀ x ∈ Metric.ball z0 r, 0 ≤ x.1 → ∀ y ∈ Metric.ball z0 r, 0 ≤ y.1 →
      dist (f x) (f y) ≤ K1 * dist x y)
    (h2 : ∀ x ∈ Metric.ball z0 r, x.1 ≤ 0 → ∀ y ∈ Metric.ball z0 r, y.1 ≤ 0 →
      dist (f x) (f y) ≤ K2 * dist x y)
    (x : R4) (hx : x ∈ Metric.ball z0 r) (hx0 : 0 ≤ x.1)
    (y : R4) (hy : y ∈ Metric.ball z0 r) (hy0 : y.1 ≤ 0) :
    dist (f x) (f y) ≤ (K1 + K2) * dist x y := by
  set t : ℝ := x.1 / (x.1 - y.1) with ht
  have ht0 : 0 ≤ t := div_nonneg hx0 (by linarith)
  have ht1 : t ≤ 1 := by
    rcases eq_or_lt_of_le (show 0 ≤ x.1 - y.1 by linarith) with h | h
    · rw [ht, ← h, div_zero]; norm_num
    · rw [ht, div_le_one h]; linarith
  set w : R4 := x + t • (y - x) with hw
  have hwb : w ∈ Metric.ball z0 r := (convex_ball z0 r).add_smul_sub_mem hx hy ⟨ht0, ht1⟩
  have hw1 : w.1 = 0 := by
    simp only [hw, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    rcases eq_or_lt_of_le (show 0 ≤ x.1 - y.1 by linarith) with h | h
    · have : x.1 = 0 := by linarith
      rw [ht, ← h, div_zero]; simp [this]
    · rw [ht]; field_simp; ring
  have e1 : dist x w = t * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, show x - w = t • (x - y) by simp only [hw]; module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have e2 : dist w y = (1 - t) * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, show w - y = (1 - t) • (x - y) by simp only [hw]; module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have a1 := h1 x hx hx0 w hwb hw1.ge
  have a2 := h2 w hwb hw1.le y hy hy0
  have hd := dist_nonneg (x := x) (y := y)
  calc dist (f x) (f y) ≤ dist (f x) (f w) + dist (f w) (f y) := dist_triangle _ _ _
    _ ≤ K1 * (t * dist x y) + K2 * ((1 - t) * dist x y) := by rw [← e1, ← e2]; linarith
    _ ≤ (K1 + K2) * dist x y := by
          have b1 := mul_nonneg (mul_nonneg hK1 hd) (sub_nonneg.mpr ht1)
          have b2 := mul_nonneg (mul_nonneg hK2 hd) ht0
          nlinarith

theorem glue_lip (f : R4 → ℝ) (z0 : R4) (r K1 K2 : ℝ) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (h1 : ∀ x ∈ Metric.ball z0 r, 0 ≤ x.1 → ∀ y ∈ Metric.ball z0 r, 0 ≤ y.1 →
      dist (f x) (f y) ≤ K1 * dist x y)
    (h2 : ∀ x ∈ Metric.ball z0 r, x.1 ≤ 0 → ∀ y ∈ Metric.ball z0 r, y.1 ≤ 0 →
      dist (f x) (f y) ≤ K2 * dist x y) :
    ∀ x ∈ Metric.ball z0 r, ∀ y ∈ Metric.ball z0 r, dist (f x) (f y) ≤ (K1 + K2) * dist x y := by
  intro x hx y hy
  have hd := dist_nonneg (x := x) (y := y)
  rcases le_total 0 x.1 with hx0 | hx0 <;> rcases le_total 0 y.1 with hy0 | hy0
  · have := h1 x hx hx0 y hy hy0; nlinarith [mul_nonneg hK2 hd]
  · exact glue_mixed f z0 r K1 K2 hK1 hK2 h1 h2 x hx hx0 y hy hy0
  · rw [dist_comm, dist_comm x]
    exact glue_mixed f z0 r K1 K2 hK1 hK2 h1 h2 y hy hy0 x hx hx0
  · have := h2 x hx hx0 y hy hy0; nlinarith [mul_nonneg hK1 hd]

/-! ### clipping -/

noncomputable def cl (w : R4) : R4 := (w.1, w.2.1, w.2.2.1, clip 1 w.2.2.2)

theorem clip_lip (a b : ℝ) : |clip 1 a - clip 1 b| ≤ |a - b| := by
  unfold clip
  simp only [max_def, min_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [le_abs_self (a - b), neg_abs_le (a - b)]

theorem cl_lip : LipschitzWith 1 cl := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, cl, Prod.dist_eq]
  gcongr
  rw [Real.dist_eq, Real.dist_eq]
  exact clip_lip _ _

section
variable (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (Bc Dc : Fin 35 → ℚ)

theorem lip_of_comp (q : R4 → R4) (z0 : R4) (hq : ContDiffAt ℝ 1 q z0)
    (hg : (q z0).1 < Real.pi / 2) :
    ∃ K : NNReal, ∃ t ∈ nhds z0, LipschitzOnWith K (fun z => Hhat4 V R Bc Dc (cl (q z))) t := by
  obtain ⟨K1, t1, ht1, hL1⟩ := (Hhat4_contDiffAt V R Bc Dc (cl (q z0)) hg).exists_lipschitzOnWith
  obtain ⟨K2, t2, ht2, hL2⟩ := hq.exists_lipschitzOnWith
  have hcont : ContinuousAt (fun z => cl (q z)) z0 :=
    cl_lip.continuous.continuousAt.comp hq.continuousAt
  refine ⟨K1 * (1 * K2), t2 ∩ (fun z => cl (q z)) ⁻¹' t1,
    Filter.inter_mem ht2 (hcont.preimage_mem_nhds ht1), ?_⟩
  exact hL1.comp ((cl_lip.comp_lipschitzOnWith hL2).mono Set.inter_subset_left)
    (fun z hz => hz.2)

theorem familyV_ext (γ a b : ℝ) (hγ : 0 ≤ γ) : familyV V γ a b = familyVExt V γ a b := by
  unfold familyV familyVExt
  have : 0 ≤ 2 * γ / Real.pi := by positivity
  simp only [bspline_eq_ext _ _ this]

theorem familyR_ext (γ a b : ℝ) (hγ : 0 ≤ γ) : familyR R γ a b = familyRExt R γ a b := by
  unfold familyR familyRExt
  have : 0 ≤ 2 * γ / Real.pi := by positivity
  simp only [bspline_eq_ext _ _ this]

theorem familySpline_ext (c : Fin 35 → ℚ) (γ : ℝ) (hγ : 0 ≤ γ) :
    familySpline c γ = familySplineExt c γ := by
  unfold familySpline familySplineExt
  have : 0 ≤ 2 * γ / Real.pi := by positivity
  simp only [bspline_eq_ext _ _ this]

theorem familyH_eq_pos (z : R4) (hz : 0 ≤ z.1) :
    familyH V R Bc Dc z = familyHhat V R Bc Dc z.1 (posA z) (posB z) (clip 1 (balanceXi z)) := by
  unfold familyH
  rw [if_pos hz]
  simp only [familyHPos, familyHhat, familyV_ext V _ _ _ hz, familyR_ext R _ _ _ hz,
    familySpline_ext _ _ hz, posA, posB, balanceXi]

theorem familyH_eq_Hplus (z : R4) (hz : 0 ≤ z.1) :
    familyH V R Bc Dc z = Hhat4 V R Bc Dc (cl (mC z)) := familyH_eq_pos V R Bc Dc z hz

theorem condH0 (hc : FamilyCoeffConditions V R Bc Dc) : CondH0 (familyH V R Bc Dc) := by
  have hLL : LocallyLipschitzOn OmegaTimesR (familyH V R Bc Dc) := by
    intro z0 hz0
    have hV : z0 ∈ Vset := omega_sub_Vset hz0
    have hV' : reflect1 z0 ∈ Vset := (reflect1_mem_Vset z0).mpr hV
    obtain ⟨K1, t1, ht1, hL1⟩ := lip_of_comp V R Bc Dc mC z0 (mC_contDiffAt z0 hV)
      (lt_of_Vset z0 hV)
    obtain ⟨K2, t2, ht2, hL2⟩ := lip_of_comp V R Bc Dc (mC ∘ reflect1) z0
      ((mC_contDiffAt _ hV').comp z0 reflect1_contDiff.contDiffAt) (lt_of_Vset _ hV')
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht1 ht2)
    refine ⟨K1 + K2, Metric.ball z0 r,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z0 hr), ?_⟩
    rw [lipschitzOnWith_iff_dist_le_mul]
    push_cast
    apply glue_lip _ z0 r _ _ K1.2 K2.2
    · intro x hx hx0 y hy hy0
      rw [familyH_eq_Hplus V R Bc Dc x hx0, familyH_eq_Hplus V R Bc Dc y hy0]
      exact hL1.dist_le_mul x (hball hx).1 y (hball hy).1
    · intro x hx hx0 y hy hy0
      rw [← familyH_reflect V R Bc Dc hc x, ← familyH_reflect V R Bc Dc hc y,
        familyH_eq_Hplus V R Bc Dc _ (by simp [reflect1]; linarith),
        familyH_eq_Hplus V R Bc Dc _ (by simp [reflect1]; linarith)]
      exact hL2.dist_le_mul x (hball hx).2 y (hball hy).2
  exact ⟨hLL.continuousOn, hLL⟩

end

end L56



namespace L56

def Kc (s : Fin 3) : Set ℝ := ![Set.Icc (-1) 1, Set.Ici 1, Set.Iic (-1)] s

theorem Kc_closed (s : Fin 3) : IsClosed (Kc s) := by
  fin_cases s <;> simp [Kc, isClosed_Icc, isClosed_Ici, isClosed_Iic]

theorem Kc_cover (x : ℝ) : ∃ s, x ∈ Kc s := by
  rcases le_total x (-1) with h | h
  · exact ⟨2, by simp [Kc, h]⟩
  rcases le_total x 1 with h' | h'
  · exact ⟨0, by simp [Kc, h, h']⟩
  · exact ⟨1, by simp [Kc, h']⟩

section
variable (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ) (Bc Dc : Fin 35 → ℚ)

noncomputable def Fp (s : Fin 3) : R4 → ℝ :=
  ![pieceHc V R Bc Dc, pieceHout V R Bc Dc 1, pieceHout V R Bc Dc (-1)] s

def Zp (s : Fin 3) : Set R4 := {z | z ∈ OmegaTimesR ∧ 0 ≤ z.1 ∧ balanceXi z ∈ Kc s}

theorem Fp_contDiffAt (s : Fin 3) (z : R4) (hz : z ∈ Vset) :
    ContDiffAt ℝ 1 (Fp V R Bc Dc s) z := by
  fin_cases s
  · exact pieceHc_contDiffAt V R Bc Dc z hz
  · exact pieceHout_contDiffAt V R Bc Dc 1 z hz
  · exact pieceHout_contDiffAt V R Bc Dc (-1) z hz

theorem Fp_agree (s : Fin 3) (z : R4) (hz : 0 ≤ z.1) (hk : balanceXi z ∈ Kc s) :
    familyH V R Bc Dc z = Fp V R Bc Dc s z := by
  rw [familyH_eq_pos V R Bc Dc z hz]
  fin_cases s
  · simp only [Kc, Fin.zero_eta, Matrix.cons_val_zero, Set.mem_Icc] at hk
    have : clip 1 (balanceXi z) = balanceXi z := by
      unfold clip; rw [min_eq_right hk.2, max_eq_right hk.1]
    simp only [Fp, Fin.zero_eta, Matrix.cons_val_zero, this]
    rfl
  · simp only [Kc, Fin.mk_one, Matrix.cons_val_one, Set.mem_Ici] at hk
    have : clip 1 (balanceXi z) = 1 := by
      unfold clip; rw [min_eq_left hk, max_eq_right (by norm_num)]
    simp only [Fp, Fin.mk_one, Matrix.cons_val_one, this]
    rfl
  · simp only [Kc, Fin.reduceFinMk, Matrix.cons_val, Set.mem_Iic] at hk
    have : clip 1 (balanceXi z) = -1 := by
      unfold clip; rw [min_eq_right (by linarith), max_eq_left hk]
    simp only [Fp, Fin.reduceFinMk, Matrix.cons_val, this]
    rfl

theorem isPieceGradient_of (s : Fin 3) (z : R4) (hz : z ∈ Zp s) :
    IsPieceGradient V R Bc Dc z (gradient4 (Fp V R Bc Dc s) z) := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨h1, h2, ?_⟩
  fin_cases s
  · simp only [Kc, Fin.zero_eta, Matrix.cons_val_zero, Set.mem_Icc] at h3
    exact Or.inl ⟨abs_le.mpr h3, rfl⟩
  · simp only [Kc, Fin.mk_one, Matrix.cons_val_one, Set.mem_Ici] at h3
    exact Or.inr (Or.inl ⟨h3, rfl⟩)
  · simp only [Kc, Fin.reduceFinMk, Matrix.cons_val, Set.mem_Iic] at h3
    exact Or.inr (Or.inr ⟨h3, rfl⟩)

noncomputable def Zf (i : Fin 6) : Set R4 :=
  if h : i.val < 3 then Zp ⟨i.val, h⟩ else reflect1 ⁻¹' Zp ⟨i.val - 3, by have := i.isLt; omega⟩

noncomputable def Ff (i : Fin 6) : R4 → ℝ :=
  if h : i.val < 3 then Fp V R Bc Dc ⟨i.val, h⟩
  else Fp V R Bc Dc ⟨i.val - 3, by have := i.isLt; omega⟩ ∘ reflect1

theorem Zp_closed (s : Fin 3) : ∃ K : Set R4, IsClosed K ∧ Zp s = K ∩ OmegaTimesR := by
  refine ⟨{z | 0 ≤ z.1 ∧ balanceXi z ∈ Kc s}, ?_, ?_⟩
  · exact (isClosed_le continuous_const continuous_fst).inter
      ((Kc_closed s).preimage balanceXi_continuous)
  · ext z; simp only [Zp, Set.mem_inter_iff, Set.mem_setOf_eq]; tauto

theorem Zp_sub (s : Fin 3) : Zp s ⊆ OmegaTimesR := fun _ h => h.1

noncomputable def Pstr (hc : FamilyCoeffConditions V R Bc Dc) :
    PiecewiseC1 (familyH V R Bc Dc) where
  m := 6
  Z := Zf
  F := Ff V R Bc Dc
  closed := by
    intro i
    unfold Zf
    split_ifs with h
    · exact Zp_closed _
    · obtain ⟨K, hK, hZ⟩ := Zp_closed ⟨i.val - 3, by have := i.isLt; omega⟩
      refine ⟨reflect1 ⁻¹' K, hK.preimage reflect1_contDiff.continuous, ?_⟩
      rw [hZ, Set.preimage_inter]
      congr 1
      ext z; exact reflect1_mem_omega z
  cover := by
    intro z hz
    rcases le_or_gt 0 z.1 with h0 | h0
    · obtain ⟨s, hs⟩ := Kc_cover (balanceXi z)
      refine ⟨⟨s.val, by omega⟩, ?_⟩
      simp only [Zf, s.isLt, dif_pos]
      exact ⟨hz, h0, hs⟩
    · obtain ⟨s, hs⟩ := Kc_cover (balanceXi (reflect1 z))
      refine ⟨⟨s.val + 3, by omega⟩, ?_⟩
      have : ¬ (s.val + 3 < 3) := by omega
      simp only [Zf, this, dif_neg, not_false_eq_true, Nat.add_sub_cancel]
      refine ⟨(reflect1_mem_omega z).mpr hz, ?_, hs⟩
      simp only [reflect1]; linarith
  smooth := by
    intro i
    refine ⟨Vset, isOpen_Vset, ?_, ?_⟩
    · unfold Zf
      split_ifs
      · exact (Zp_sub _).trans omega_sub_Vset
      · intro z hz
        exact (reflect1_mem_Vset z).mp (omega_sub_Vset (Zp_sub _ hz))
    · intro z hz
      apply ContDiffAt.contDiffWithinAt
      unfold Ff
      split_ifs
      · exact Fp_contDiffAt V R Bc Dc _ z hz
      · exact (Fp_contDiffAt V R Bc Dc _ _ ((reflect1_mem_Vset z).mpr hz)).comp z
          reflect1_contDiff.contDiffAt
  agree := by
    intro i z hz
    unfold Zf at hz
    unfold Ff
    split_ifs with h
    · rw [dif_pos h] at hz
      exact Fp_agree V R Bc Dc _ z hz.2.1 hz.2.2
    · rw [dif_neg h] at hz
      rw [← familyH_reflect V R Bc Dc hc z]
      exact Fp_agree V R Bc Dc _ _ hz.2.1 hz.2.2

end

end L56

theorem solution (V : Fin 12 → Fin 12 → Fin 35 → ℚ) (R : Fin 6 → Fin 6 → Fin 35 → ℚ)
    (Bc Dc : Fin 35 → ℚ) (hc : FamilyCoeffConditions V R Bc Dc) :
    ∃ P : PiecewiseC1 (familyH V R Bc Dc), CondH0 (familyH V R Bc Dc) ∧
      ∀ z ∈ OmegaTimesR, ∀ g : R4, P.IncidentGradient z g →
        IsPieceGradient V R Bc Dc z g ∨
        (IsPieceGradient V R Bc Dc (reflect1 z) (-g.1, -g.2.1, g.2.2.1, -g.2.2.2) ∧
          ∀ U : ℝ, pencilResidual U (familyH V R Bc Dc) (-g.1, -g.2.1, g.2.2.1, -g.2.2.2)
              (reflect1 z) = pencilResidual U (familyH V R Bc Dc) g z) := by
  refine ⟨L56.Pstr V R Bc Dc hc, L56.condH0 V R Bc Dc hc, ?_⟩
  rintro z hz g ⟨i, hzi, hg⟩
  change z ∈ L56.Zf i at hzi
  change g = gradient4 (L56.Ff V R Bc Dc i) z at hg
  unfold L56.Zf at hzi
  unfold L56.Ff at hg
  split_ifs at hzi hg with h
  · left
    rw [hg]
    exact L56.isPieceGradient_of V R Bc Dc _ z hzi
  · right
    set s : Fin 3 := ⟨i.val - 3, by have := i.isLt; omega⟩
    have hV : reflect1 z ∈ L56.Vset := L56.omega_sub_Vset (L56.Zp_sub _ hzi)
    have hd := (L56.Fp_contDiffAt V R Bc Dc s _ hV).differentiableAt one_ne_zero
    have hgr := L56.gradient4_reflect _ z hd
    rw [← hg] at hgr
    have hg' : (-g.1, -g.2.1, g.2.2.1, -g.2.2.2) = gradient4 (L56.Fp V R Bc Dc s) (reflect1 z) := by
      rw [hgr]; simp
    rw [hg']
    refine ⟨L56.isPieceGradient_of V R Bc Dc s _ hzi, fun U => ?_⟩
    rw [← hg']
    exact L56.pencil_reflect U _ g z (L56.familyH_reflect V R Bc Dc hc z)
