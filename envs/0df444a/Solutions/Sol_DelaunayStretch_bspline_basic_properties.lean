-- Prove2me | solution 1 for DelaunayStretch.bspline_basic_properties
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:56:14.776499+00:00
-- url     : https://prove2.me/submissions/5b1a2f1f-9cec-4c92-9005-d415eaa18177

import Mathlib
import Definitions.Def_DelaunayStretch_FamilyPieces

open DelaunayStretch

namespace BBP

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

theorem checkB : ∀ k < 31, ∀ d < 5,
    bpolyQ k 3 (k + d) (((k:ℚ) + 1) / 32) = bpolyQ (k + 1) 3 (k + d) (((k:ℚ) + 1) / 32) := by
  decide +kernel

theorem checkD : ∀ k < 31, ∀ d < 5,
    dpolyQ k 3 (k + d) (((k:ℚ) + 1) / 32) = dpolyQ (k + 1) 3 (k + d) (((k:ℚ) + 1) / 32) := by
  decide +kernel

def ddpolyQ (k : ℕ) : ℕ → ℕ → ℚ → ℚ
  | 0, _, _ => 0
  | p + 1, j, τ =>
      2 / (knotQ (j + p + 1) - knotQ j) * dpolyQ k p j τ +
      (τ - knotQ j) / (knotQ (j + p + 1) - knotQ j) * ddpolyQ k p j τ +
        2 * (-1) / (knotQ (j + p + 2) - knotQ (j + 1)) * dpolyQ k p (j + 1) τ +
        (knotQ (j + p + 2) - τ) / (knotQ (j + p + 2) - knotQ (j + 1)) * ddpolyQ k p (j + 1) τ

theorem checkDD : ∀ k < 31, ∀ d < 5,
    ddpolyQ k 3 (k + d) (((k:ℚ) + 1) / 32) = ddpolyQ (k + 1) 3 (k + d) (((k:ℚ) + 1) / 32) := by
  decide +kernel

end BBP

namespace BBA

/-! ## Part 1. Cubic B-splines: local polynomial pieces, nonnegativity, partition of unity -/

/-- Polynomials in one variable as coefficient lists (lowest degree first). -/
def padd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

/-- `(a + b s) * p`. -/
def pmulLin (a b : ℚ) (p : List ℚ) : List ℚ := padd (p.map (a * ·)) (0 :: p.map (b * ·))

/-- Evaluation of a coefficient list at a real point (Horner). -/
noncomputable def peval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: p, s => (c : ℝ) + s * peval p s

lemma peval_padd : ∀ (p q : List ℚ) (s : ℝ), peval (padd p q) s = peval p s + peval q s
  | [], q, s => by simp [padd, peval]
  | a :: p, [], s => by simp [padd, peval]
  | a :: p, b :: q, s => by
      simp only [padd, peval, peval_padd p q s]; push_cast; ring

lemma peval_map (a : ℚ) : ∀ (p : List ℚ) (s : ℝ), peval (p.map (a * ·)) s = a * peval p s
  | [], s => by simp [peval]
  | c :: p, s => by
      simp only [List.map_cons, peval, peval_map a p s]; push_cast; ring

lemma peval_pmulLin (a b : ℚ) (p : List ℚ) (s : ℝ) :
    peval (pmulLin a b p) s = ((a : ℝ) + b * s) * peval p s := by
  simp only [pmulLin, peval_padd, peval, peval_map]; push_cast; ring

/-- Rational copy of `splineKnot`. -/
def knotQ (j : ℕ) : ℚ := max 0 (min 1 (((j : ℚ) - 3) / 32))

lemma knotQ_cast (j : ℕ) : ((knotQ j : ℚ) : ℝ) = splineKnot j := by
  simp [knotQ, splineKnot]

/-- The polynomial (in the local variable `s = 32 τ - k`) representing the B-spline
`N_{j,p}` on the knot interval `[k/32, (k+1)/32]`. -/
def bpoly (k : ℕ) : ℕ → ℕ → List ℚ
  | 0, j => [if j = k + 3 then 1 else 0]
  | p + 1, j =>
      padd (pmulLin (((k : ℚ) / 32 - knotQ j) / (knotQ (j + p + 1) - knotQ j))
                    ((1 / 32) / (knotQ (j + p + 1) - knotQ j)) (bpoly k p j))
           (pmulLin ((knotQ (j + p + 2) - (k : ℚ) / 32) / (knotQ (j + p + 2) - knotQ (j + 1)))
                    ((-1 / 32) / (knotQ (j + p + 2) - knotQ (j + 1))) (bpoly k p (j + 1)))

lemma splineKnot_mono {i j : ℕ} (h : i ≤ j) : splineKnot i ≤ splineKnot j := by
  unfold splineKnot
  have : ((i : ℝ) - 3) / 32 ≤ ((j : ℝ) - 3) / 32 := by
    have : (i : ℝ) ≤ j := by exact_mod_cast h
    linarith
  exact max_le_max le_rfl (min_le_min le_rfl this)

lemma splineKnot_le_one (j : ℕ) : splineKnot j ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma splineKnot_k3 (k : ℕ) (hk : k ≤ 32) : splineKnot (k + 3) = (k : ℝ) / 32 := by
  unfold splineKnot
  have h1 : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  rw [show ((k : ℝ) + 3 - 3) / 32 = (k : ℝ) / 32 by ring]
  rw [min_eq_right (by linarith), max_eq_right (by positivity)]

lemma splineKnot_k4 (k : ℕ) (hk : k ≤ 31) : splineKnot (k + 3 + 1) = ((k : ℝ) + 1) / 32 := by
  have := splineKnot_k3 (k + 1) (by omega)
  rw [show k + 3 + 1 = k + 1 + 3 by ring, this]; push_cast; ring

lemma deg0_local (k : ℕ) (hk : k ≤ 31) (τ : ℝ) (h0 : (k : ℝ) / 32 ≤ τ)
    (h1 : τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) (j : ℕ) :
    bsplineDeg0 j τ = if j = k + 3 then 1 else 0 := by
  have hk' : (k : ℝ) ≤ 31 := by exact_mod_cast hk
  unfold bsplineDeg0
  by_cases hj : j = k + 3
  · subst hj
    rw [if_pos rfl, if_pos]
    rcases h1 with h1 | ⟨h31, hτ⟩
    · left
      rw [splineKnot_k3 k (by omega), splineKnot_k4 k hk]
      exact ⟨h0, h1⟩
    · right; exact ⟨by omega, hτ⟩
  · rw [if_neg hj, if_neg]
    rintro (⟨ha, hb⟩ | ⟨hj34, hτ⟩)
    · rcases h1 with h1 | ⟨h31, hτ⟩
      · rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
        · have := splineKnot_mono (show j + 1 ≤ k + 3 by omega)
          rw [splineKnot_k3 k (by omega)] at this
          linarith
        · have := splineKnot_mono (show k + 3 + 1 ≤ j by omega)
          rw [splineKnot_k4 k hk] at this
          linarith
      · have := splineKnot_le_one (j + 1)
        linarith
    · rcases h1 with h1 | ⟨h31, hτ'⟩
      · linarith
      · omega

lemma basis_local (k : ℕ) (hk : k ≤ 31) (τ : ℝ) (h0 : (k : ℝ) / 32 ≤ τ)
    (h1 : τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) :
    ∀ p j, bsplineBasis p j τ = peval (bpoly k p j) (32 * τ - k)
  | 0, j => by
      rw [bsplineBasis, deg0_local k hk τ h0 h1 j]
      simp only [bpoly, peval]
      split_ifs <;> simp
  | p + 1, j => by
      rw [bsplineBasis, bpoly, peval_padd, peval_pmulLin, peval_pmulLin,
        ← basis_local k hk τ h0 h1 p j, ← basis_local k hk τ h0 h1 p (j + 1)]
      push_cast [knotQ_cast]
      ring

lemma peval_bpoly_zero (k : ℕ) (s : ℝ) : ∀ p j, k + 3 < j → peval (bpoly k p j) s = 0
  | 0, j, hj => by
      simp only [bpoly, peval]
      rw [if_neg (by omega)]; simp
  | p + 1, j, hj => by
      rw [bpoly, peval_padd, peval_pmulLin, peval_pmulLin, peval_bpoly_zero k s p j hj,
        peval_bpoly_zero k s p (j + 1) (by omega)]
      ring

/-- Nonnegativity of the four Bernstein coefficients of a cubic on `[0, 1]`. -/
def cubicOK : List ℚ → Bool
  | [c0, c1, c2, c3] =>
      decide (0 ≤ c0) && decide (0 ≤ c0 + c1 / 3) && decide (0 ≤ c0 + 2 * c1 / 3 + c2 / 3) &&
        decide (0 ≤ c0 + c1 + c2 + c3)
  | _ => false

lemma cubic_nonneg (p : List ℚ) (h : cubicOK p = true) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ peval p s := by
  rcases p with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, p⟩⟩⟩⟩⟩ <;>
    simp only [cubicOK, Bool.false_eq_true] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have e : peval [c0, c1, c2, c3] s =
      (c0 : ℝ) * (1 - s) ^ 3 + 3 * ((c0 + c1 / 3 : ℚ) : ℝ) * s * (1 - s) ^ 2 +
        3 * ((c0 + 2 * c1 / 3 + c2 / 3 : ℚ) : ℝ) * s ^ 2 * (1 - s) +
        ((c0 + c1 + c2 + c3 : ℚ) : ℝ) * s ^ 3 := by
    simp only [peval]; push_cast; ring
  have a0 : (0 : ℝ) ≤ (c0 : ℝ) := by exact_mod_cast h0
  have a1 : (0 : ℝ) ≤ ((c0 + c1 / 3 : ℚ) : ℝ) := by exact_mod_cast h1
  have a2 : (0 : ℝ) ≤ ((c0 + 2 * c1 / 3 + c2 / 3 : ℚ) : ℝ) := by exact_mod_cast h2
  have a3 : (0 : ℝ) ≤ ((c0 + c1 + c2 + c3 : ℚ) : ℝ) := by exact_mod_cast h3
  have hs' : 0 ≤ 1 - s := by linarith
  rw [e]
  have t0 := mul_nonneg a0 (pow_nonneg hs' 3)
  have t1 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) a1) hs0)
    (pow_nonneg hs' 2)
  have t2 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) a2)
    (pow_nonneg hs0 2)) hs'
  have t3 := mul_nonneg a3 (pow_nonneg hs0 3)
  linarith

lemma peval_bpoly_zero_low (k : ℕ) (s : ℝ) : ∀ p j, j + p < k + 3 → peval (bpoly k p j) s = 0
  | 0, j, hj => by
      simp only [bpoly, peval]
      rw [if_neg (by omega)]; simp
  | p + 1, j, hj => by
      rw [bpoly, peval_padd, peval_pmulLin, peval_pmulLin,
        peval_bpoly_zero_low k s p j (by omega), peval_bpoly_zero_low k s p (j + 1) (by omega)]
      ring

theorem check_nonneg : ∀ k < 32, ∀ d < 4, cubicOK (bpoly k 3 (k + d)) = true := by
  decide +kernel

theorem check_pou : ∀ k < 32,
    padd (padd (padd (bpoly k 3 k) (bpoly k 3 (k + 1))) (bpoly k 3 (k + 2))) (bpoly k 3 (k + 3))
      = [1, 0, 0, 0] := by
  decide +kernel

lemma exists_interval (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    ∃ k : ℕ, k ≤ 31 ∧ (k : ℝ) / 32 ≤ τ ∧ (τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) := by
  by_cases hτ : τ = 1
  · refine ⟨31, le_rfl, ?_, Or.inr ⟨rfl, hτ⟩⟩
    rw [hτ]; norm_num
  · have hlt : τ < 1 := lt_of_le_of_ne h1 hτ
    have hf1 := Nat.floor_le (show (0 : ℝ) ≤ 32 * τ by linarith)
    have hf2 := Nat.lt_floor_add_one (32 * τ)
    refine ⟨⌊32 * τ⌋₊, ?_, ?_, Or.inl ?_⟩
    · have : (⌊32 * τ⌋₊ : ℝ) < 32 := by linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    · linarith
    · linarith

lemma local_s_bounds (k : ℕ) (τ : ℝ) (h0 : (k : ℝ) / 32 ≤ τ)
    (h1 : τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) :
    0 ≤ 32 * τ - k ∧ 32 * τ - k ≤ 1 := by
  constructor
  · linarith
  · rcases h1 with h1 | ⟨h31, hτ⟩
    · linarith
    · subst h31; rw [hτ]; norm_num

/-- **Nonnegativity of the cubic B-splines** on `[0, 1]`. -/
theorem bspline_nonneg (l : ℕ) (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) : 0 ≤ bspline l τ := by
  obtain ⟨k, hk, hk0, hk1⟩ := exists_interval τ h0 h1
  rw [bspline, basis_local k hk τ hk0 hk1]
  obtain ⟨hs0, hs1⟩ := local_s_bounds k τ hk0 hk1
  by_cases hl1 : l < k
  · rw [peval_bpoly_zero_low k _ 3 l (by omega)]
  by_cases hl2 : k + 3 < l
  · rw [peval_bpoly_zero k _ 3 l hl2]
  obtain ⟨d, rfl⟩ : ∃ d, l = k + d := ⟨l - k, by omega⟩
  exact cubic_nonneg _ (check_nonneg k (by omega) d (by omega)) _ hs0 hs1

/-- **Partition of unity of the cubic B-splines** on `[0, 1]`. -/
theorem bspline_sum_one (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    ∑ l : Fin 35, bspline l τ = 1 := by
  obtain ⟨k, hk, hk0, hk1⟩ := exists_interval τ h0 h1
  rw [Fin.sum_univ_eq_sum_range (fun l => bspline l τ) 35]
  simp only [bspline, basis_local k hk τ hk0 hk1]
  rw [← Finset.sum_subset (s₁ := Finset.Ico k (k + 4))]
  · rw [Finset.sum_Ico_eq_sum_range, show k + 4 - k = 4 by omega]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
    rw [← peval_padd, ← peval_padd, ← peval_padd, check_pou k (by omega)]
    simp [peval]
  · intro x hx
    simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
    omega
  · intro x _ hx
    simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hx
    rcases hx with hx | hx
    · exact peval_bpoly_zero_low k _ 3 x (by omega)
    · exact peval_bpoly_zero k _ 3 x (by omega)

end BBA



namespace BBP

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


noncomputable def ddpolyR (k : ℕ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | p + 1, j, τ =>
      2 / ((knotQ (j + p + 1) : ℝ) - knotQ j) * dpolyR k p j τ +
      (τ - knotQ j) / ((knotQ (j + p + 1) : ℝ) - knotQ j) * ddpolyR k p j τ +
        2 * (-1) / ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1)) * dpolyR k p (j + 1) τ +
        ((knotQ (j + p + 2) : ℝ) - τ) / ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1)) *
          ddpolyR k p (j + 1) τ

theorem ddpolyR_cast (k p j : ℕ) (q : ℚ) : ddpolyR k p j (q : ℝ) = (ddpolyQ k p j q : ℝ) := by
  induction p generalizing j with
  | zero => simp [ddpolyR, ddpolyQ]
  | succ p ih => simp [ddpolyR, ddpolyQ, ih, dpolyR_cast]

theorem dpolyR_hasDerivAt (k p j : ℕ) (τ : ℝ) :
    HasDerivAt (dpolyR k p j) (ddpolyR k p j τ) τ := by
  induction p generalizing j with
  | zero => exact hasDerivAt_const _ _
  | succ p ih =>
    have hb1 := bpolyR_hasDerivAt k p j τ
    have hb2 := bpolyR_hasDerivAt k p (j + 1) τ
    have h1 := (((hb1.const_mul (1 / ((knotQ (j + p + 1) : ℝ) - knotQ j))).add
      ((((hasDerivAt_id τ).sub_const (knotQ j : ℝ)).div_const
      ((knotQ (j + p + 1) : ℝ) - knotQ j)).mul (ih j))).add
      (hb2.const_mul ((-1) / ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1))))).add
      ((((hasDerivAt_id τ).const_sub (knotQ (j + p + 2) : ℝ)).div_const
      ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1))).mul (ih (j + 1)))
    have h2 : HasDerivAt (dpolyR k (p+1) j) _ τ := h1.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by simp [dpolyR])
    exact h2.congr_deriv (by simp only [ddpolyR, id]; ring)

theorem bpolyR_contDiff2 (k p j : ℕ) : ContDiff ℝ 2 (bpolyR k p j) := by
  induction p generalizing j with
  | zero => exact contDiff_const
  | succ p ih =>
    have h1 := ih j
    have h2 := ih (j + 1)
    show ContDiff ℝ 2 (fun τ => (τ - knotQ j) / ((knotQ (j + p + 1) : ℝ) - knotQ j) * bpolyR k p j τ +
        ((knotQ (j + p + 2) : ℝ) - τ) / ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1)) *
          bpolyR k p (j + 1) τ)
    fun_prop

theorem deriv_bpolyR (k p j : ℕ) : deriv (bpolyR k p j) = dpolyR k p j :=
  funext fun τ => (bpolyR_hasDerivAt k p j τ).deriv

theorem deriv_dpolyR (k p j : ℕ) : deriv (dpolyR k p j) = ddpolyR k p j :=
  funext fun τ => (dpolyR_hasDerivAt k p j τ).deriv

theorem bpolyR_zero_high (k : ℕ) (τ : ℝ) : ∀ p j, k + 3 < j → bpolyR k p j τ = 0
  | 0, j, hj => by simp only [bpolyR]; rw [if_neg (by omega)]
  | p + 1, j, hj => by
      simp only [bpolyR]
      rw [bpolyR_zero_high k τ p j hj, bpolyR_zero_high k τ p (j + 1) (by omega)]
      ring

/-- derivative of a glued function -/
theorem glue_hasDeriv (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (c : ℝ)
    (h0 : u c = v c) (h1 : deriv u c = deriv v c) (x : ℝ) :
    HasDerivAt (fun x => if x < c then u x else v x)
      (if x < c then deriv u x else deriv v x) x := by
  set g := fun x => if x < c then u x else v x with hg
  have hud : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  rcases lt_trichotomy x c with hx | hx | hx
  · have : g =ᶠ[nhds x] u := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [hg, show y < c from hy]
    rw [if_pos hx]
    exact (hud x).hasDerivAt.congr_of_eventuallyEq this
  · subst hx
    rw [if_neg (lt_irrefl x)]
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
    rw [if_neg (not_lt.mpr hx.le)]
    exact (hvd x).hasDerivAt.congr_of_eventuallyEq this

theorem glue_C1 (u v : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (c : ℝ)
    (h0 : u c = v c) (h1 : deriv u c = deriv v c) :
    ContDiff ℝ 1 (fun x => if x < c then u x else v x) := by
  have hder := glue_hasDeriv u v hu hv c h0 h1
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hder x).differentiableAt, ?_⟩
  have : deriv (fun x => if x < c then u x else v x) =
      fun x => if c ≤ x then deriv v x else deriv u x := by
    funext x; rw [(hder x).deriv]
    by_cases hx : x < c
    · simp [hx, not_le.mpr hx]
    · simp [hx, not_lt.mp hx]
  rw [this]
  exact Continuous.if_le (hv.continuous_deriv le_rfl) (hu.continuous_deriv le_rfl)
    continuous_const continuous_id (fun x hx => by rw [← hx, h1])

theorem glue_C2 (u v : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (c : ℝ)
    (h0 : u c = v c) (h1 : deriv u c = deriv v c)
    (h2 : deriv (deriv u) c = deriv (deriv v) c) :
    ContDiff ℝ 2 (fun x => if x < c then u x else v x) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hder := glue_hasDeriv u v hu1 hv1 c h0 h1
  have hu' : ContDiff ℝ 1 (deriv u) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) u from hu)).2.2
  have hv' : ContDiff ℝ 1 (deriv v) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) v from hv)).2.2
  show ContDiff ℝ (1 + 1) _
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (hder x).differentiableAt, by simp, ?_⟩
  have : deriv (fun x => if x < c then u x else v x) =
      fun x => if x < c then deriv u x else deriv v x := funext fun x => (hder x).deriv
  rw [this]
  exact glue_C1 _ _ hu' hv' c h1 h2

theorem bpolyR_zero_low (k : ℕ) (τ : ℝ) : ∀ p j, j + p < k + 3 → bpolyR k p j τ = 0
  | 0, j, hj => by simp only [bpolyR]; rw [if_neg (by omega)]
  | p + 1, j, hj => by
      simp only [bpolyR]
      rw [bpolyR_zero_low k τ p j (by omega), bpolyR_zero_low k τ p (j + 1) (by omega)]
      ring

/-- reduce a knot statement to the five relevant B-splines -/
theorem knot_reduce (m l : ℕ) (P : (ℝ → ℝ) → (ℝ → ℝ) → Prop) (hP : P (fun _ => 0) (fun _ => 0))
    (h : ∀ d < 5, P (bpolyR m 3 (m + d)) (bpolyR (m + 1) 3 (m + d))) :
    P (bpolyR m 3 l) (bpolyR (m + 1) 3 l) := by
  by_cases h1 : l < m
  · have e1 : bpolyR m 3 l = fun _ => 0 := funext fun τ => bpolyR_zero_low m τ 3 l (by omega)
    have e2 : bpolyR (m + 1) 3 l = fun _ => 0 :=
      funext fun τ => bpolyR_zero_low (m + 1) τ 3 l (by omega)
    rw [e1, e2]; exact hP
  by_cases h2 : m + 4 < l
  · have e1 : bpolyR m 3 l = fun _ => 0 := funext fun τ => bpolyR_zero_high m τ 3 l (by omega)
    have e2 : bpolyR (m + 1) 3 l = fun _ => 0 :=
      funext fun τ => bpolyR_zero_high (m + 1) τ 3 l (by omega)
    rw [e1, e2]; exact hP
  obtain ⟨d, rfl⟩ : ∃ d, l = m + d := ⟨l - m, by omega⟩
  exact h d (by omega)

theorem knot_value (m l : ℕ) (hm : m < 31) :
    bpolyR m 3 l (((m : ℝ) + 1) / 32) = bpolyR (m + 1) 3 l (((m : ℝ) + 1) / 32) := by
  refine knot_reduce m l (fun u v => u (((m : ℝ) + 1) / 32) = v (((m : ℝ) + 1) / 32)) rfl ?_
  intro d hd
  have h := checkB m hm d hd
  have e : (((m : ℝ) + 1) / 32) = ((((m : ℚ) + 1) / 32 : ℚ) : ℝ) := by push_cast; ring
  beta_reduce
  rw [e, bpolyR_cast, bpolyR_cast, h]

theorem knot_deriv (m l : ℕ) (hm : m < 31) :
    deriv (bpolyR m 3 l) (((m : ℝ) + 1) / 32) =
      deriv (bpolyR (m + 1) 3 l) (((m : ℝ) + 1) / 32) := by
  refine knot_reduce m l
    (fun u v => deriv u (((m : ℝ) + 1) / 32) = deriv v (((m : ℝ) + 1) / 32)) rfl ?_
  intro d hd
  have h := checkD m hm d hd
  beta_reduce
  rw [deriv_bpolyR, deriv_bpolyR]
  have e : (((m : ℝ) + 1) / 32) = ((((m : ℚ) + 1) / 32 : ℚ) : ℝ) := by push_cast; ring
  rw [e, dpolyR_cast, dpolyR_cast, h]

theorem knot_dd (m l : ℕ) (hm : m < 31) :
    deriv (deriv (bpolyR m 3 l)) (((m : ℝ) + 1) / 32) =
      deriv (deriv (bpolyR (m + 1) 3 l)) (((m : ℝ) + 1) / 32) := by
  refine knot_reduce m l (fun u v => deriv (deriv u) (((m : ℝ) + 1) / 32) =
    deriv (deriv v) (((m : ℝ) + 1) / 32)) rfl ?_
  intro d hd
  have h := checkDD m hm d hd
  beta_reduce
  rw [deriv_bpolyR, deriv_bpolyR, deriv_dpolyR, deriv_dpolyR]
  have e : (((m : ℝ) + 1) / 32) = ((((m : ℚ) + 1) / 32 : ℚ) : ℝ) := by push_cast; ring
  rw [e, ddpolyR_cast, ddpolyR_cast, h]

theorem bsplineExt_contDiffAt (l : ℕ) (x : ℝ) (hx : x < 1) :
    ContDiffAt ℝ 2 (bsplineExt l) x := by
  by_cases h0 : x < 1 / 32
  · have : bsplineExt l =ᶠ[nhds x] bpolyR 0 3 l := by
      filter_upwards [Iio_mem_nhds h0] with y hy
      exact bsplineExt_eq 0 (by norm_num) y ⟨Or.inl rfl, by simpa using hy⟩ l
    exact ((bpolyR_contDiff2 0 3 l).contDiffAt).congr_of_eventuallyEq this
  push Not at h0
  obtain ⟨n, hn1, hn2, hn3⟩ : ∃ n : ℕ, (n : ℝ) ≤ 32 * x ∧ 32 * x < n + 1 ∧ 1 ≤ n :=
    ⟨⌊32 * x⌋₊, Nat.floor_le (by linarith), Nat.lt_floor_add_one _,
      Nat.le_floor (by push_cast; linarith)⟩
  have hn4 : n ≤ 31 := by
    have : (n : ℝ) < 32 := by linarith
    have : n < 32 := by exact_mod_cast this
    omega
  by_cases he : (n : ℝ) = 32 * x
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m < 31 := by omega
    have hxe : x = ((m : ℝ) + 1) / 32 := by push_cast at he; linarith
    have hlo : (m : ℝ) / 32 < x := by rw [hxe]; linarith
    have hhi : x < ((m : ℝ) + 2) / 32 := by rw [hxe]; linarith
    set c := ((m : ℝ) + 1) / 32
    have hg := glue_C2 (bpolyR m 3 l) (bpolyR (m + 1) 3 l) (bpolyR_contDiff2 _ _ _)
      (bpolyR_contDiff2 _ _ _) c (knot_value m l hm) (knot_deriv m l hm) (knot_dd m l hm)
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
    exact ((bpolyR_contDiff2 n 3 l).contDiffAt).congr_of_eventuallyEq this

theorem basis_eq_ext (τ : ℝ) (hτ : 0 ≤ τ) (p j : ℕ) :
    bsplineBasis p j τ = bsplineBasisExt p j τ := by
  induction p generalizing j with
  | zero => simp [bsplineBasis, bsplineBasisExt, bsplineDeg0Ext, not_lt.mpr hτ]
  | succ p ih => simp only [bsplineBasis, bsplineBasisExt, ih]

theorem bspline_eq_ext (l : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) : bspline l τ = bsplineExt l τ :=
  basis_eq_ext τ hτ 3 l

theorem basis_one (p j : ℕ) : bsplineBasis p j 1 = bpolyR 31 p j 1 := by
  induction p generalizing j with
  | zero =>
    simp only [bsplineBasis, bpolyR]
    exact BBA.deg0_local 31 le_rfl 1 (by norm_num) (Or.inr ⟨rfl, rfl⟩) j
  | succ p ih => simp only [bsplineBasis, bpolyR, splineKnot_eq, ih]

open Polynomial in
noncomputable def bpolyP (k : ℕ) : ℕ → ℕ → Polynomial ℝ
  | 0, j => C (if j = k + 3 then 1 else 0)
  | p + 1, j =>
      C (1 / ((knotQ (j + p + 1) : ℝ) - knotQ j)) * (X - C (knotQ j : ℝ)) * bpolyP k p j +
        C (1 / ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1))) * (C (knotQ (j + p + 2) : ℝ) - X) *
          bpolyP k p (j + 1)

open Polynomial in
theorem bpolyP_eval (k p j : ℕ) (τ : ℝ) : (bpolyP k p j).eval τ = bpolyR k p j τ := by
  induction p generalizing j with
  | zero => simp only [bpolyP, bpolyR]; split_ifs <;> simp
  | succ p ih =>
    simp only [bpolyP, bpolyR, eval_add, eval_mul, eval_C, eval_sub, eval_X, ih]
    ring

open Polynomial in
theorem bpolyP_natDegree (k p j : ℕ) : (bpolyP k p j).natDegree ≤ p := by
  induction p generalizing j with
  | zero => simp only [bpolyP]; split_ifs <;> simp
  | succ p ih =>
    simp only [bpolyP]
    apply natDegree_add_le_of_degree_le
    · refine (natDegree_mul_le).trans ?_
      have : (C (1 / ((knotQ (j + p + 1) : ℝ) - knotQ j)) * (X - C (knotQ j : ℝ))).natDegree ≤ 1 :=
        (natDegree_mul_le).trans (by simp)
      have := ih j
      omega
    · refine (natDegree_mul_le).trans ?_
      have : (C (1 / ((knotQ (j + p + 2) : ℝ) - knotQ (j + 1))) *
          (C (knotQ (j + p + 2) : ℝ) - X)).natDegree ≤ 1 := by
        refine (natDegree_mul_le).trans ?_
        have := natDegree_sub_le (C (knotQ (j + p + 2) : ℝ)) (X : Polynomial ℝ)
        simp at this ⊢
        exact this
      have := ih (j + 1)
      omega

end BBP

theorem solution :
    (∀ (l : ℕ) (τ : ℝ), 0 ≤ τ → τ ≤ 1 → 0 ≤ bspline l τ) ∧
    (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∑ l : Fin 35, bspline l τ = 1) ∧
    (∀ (l i : ℕ), i < 32 → ∃ p : Polynomial ℝ, p.natDegree ≤ 3 ∧
      ∀ τ ∈ Set.Icc ((i : ℝ) / 32) (((i : ℝ) + 1) / 32), bspline l τ = p.eval τ) ∧
    (∀ l : ℕ, ContDiffOn ℝ 2 (bsplineExt l) (Set.Iio 1)) := by
  refine ⟨BBA.bspline_nonneg, BBA.bspline_sum_one, ?_, ?_⟩
  · intro l i hi
    refine ⟨BBP.bpolyP i 3 l, BBP.bpolyP_natDegree i 3 l, ?_⟩
    rintro τ ⟨h0, h1⟩
    rw [BBP.bpolyP_eval]
    have hτ0 : 0 ≤ τ := le_trans (by positivity) h0
    rcases lt_or_eq_of_le h1 with h1 | h1
    · rw [BBP.bspline_eq_ext l τ hτ0]
      exact BBP.bsplineExt_eq i (by omega) τ ⟨Or.inr h0, h1⟩ l
    · subst h1
      by_cases hi' : i < 31
      · rw [BBP.bspline_eq_ext l _ hτ0,
          BBP.bsplineExt_eq (i + 1) (by omega) _ ⟨Or.inr (le_of_eq (by push_cast; ring)), by push_cast; linarith⟩ l,
          BBP.knot_value i l hi']
      · have : i = 31 := by omega
        subst this
        norm_num
        exact BBP.basis_one 3 l
  · intro l x hx
    exact (BBP.bsplineExt_contDiffAt l x hx).contDiffWithinAt
