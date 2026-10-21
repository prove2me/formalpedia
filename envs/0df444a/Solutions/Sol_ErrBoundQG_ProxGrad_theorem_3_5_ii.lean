-- Prove2me | solution 1 for ErrBoundQG.ProxGrad.theorem_3_5_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:14:29.091998+00:00
-- url     : https://prove2.me/submissions/53d52b46-232a-4bb8-9101-853da02535a6

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

set_option autoImplicit false
open ThreeOpSplitting.Convergence

theorem solution {n : ℕ} (G Φ : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hG : ThreeOpSplitting.Convergence.IsMaximalMonotone G)
    (hΦ : ThreeOpSplitting.Convergence.IsMaximalMonotone Φ)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, Φ x = (fun w => F x + w) '' G x)
    (t : ℝ) (ht : 0 < t) (JG : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hJG : ThreeOpSplitting.Convergence.IsResolvent t G JG)
    (β : ℝ) (hβ : 0 ≤ β) (hFL : ∀ x y, ‖F x - F y‖ ≤ β * ‖x - y‖)
    (JΦ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hJΦ : ThreeOpSplitting.Convergence.IsResolvent t Φ JΦ) :
    ∀ x, (1 - β * t) * ‖t⁻¹ • (x - JG (x - t • F x))‖ ≤ ‖t⁻¹ • (x - JΦ x)‖ ∧
      ‖t⁻¹ • (x - JΦ x)‖ ≤ (1 + β * t) * ‖t⁻¹ • (x - JG (x - t • F x))‖ := by
  intro x
  set p := JG (x - t • F x) with hp
  set q := JΦ x with hq
  set g : EuclideanSpace ℝ (Fin n) := t⁻¹ • (x - p) with hg
  set k : EuclideanSpace ℝ (Fin n) := t⁻¹ • (x - q) with hk
  have ht0 : t ≠ 0 := ht.ne'
  have hu : t⁻¹ • ((x - t • F x) - p) ∈ G p := hJG (x - t • F x)
  have hu' : t⁻¹ • ((x - t • F x) - p) = g - F x := by
    have : x - t • F x - p = (x - p) - t • F x := by abel
    rw [hg, this, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [hu'] at hu
  have hφp : F p + (g - F x) ∈ Φ p := by
    rw [hF p]; exact ⟨_, hu, rfl⟩
  have hkq : k ∈ Φ q := hJΦ x
  have hmon := hΦ.1 p q _ _ hφp hkq
  have hxp : x - p = t • g := by rw [hg, smul_smul, mul_inv_cancel₀ ht0, one_smul]
  have hxq : x - q = t • k := by rw [hk, smul_smul, mul_inv_cancel₀ ht0, one_smul]
  have hpq : p - q = -(t • (g - k)) := by
    have : p - q = (x - q) - (x - p) := by abel
    rw [this, hxp, hxq, smul_sub]; abel
  rw [hpq] at hmon
  have h1 : inner ℝ (-(t • (g - k))) (F p + (g - F x) - k) = -t * inner ℝ (g - k) ((g - k) - (F x - F p)) := by
    rw [inner_neg_left, real_inner_smul_left]
    have : F p + (g - F x) - k = (g - k) - (F x - F p) := by abel
    rw [this]; ring
  rw [h1] at hmon
  have h2 : ‖g - k‖ ^ 2 ≤ inner ℝ (g - k) (F x - F p) := by
    have : inner ℝ (g - k) ((g - k) - (F x - F p)) ≤ 0 := by nlinarith
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at this
    linarith
  have h3 := real_inner_le_norm (g - k) (F x - F p)
  have h4 : ‖g - k‖ ≤ ‖F x - F p‖ := by
    by_cases h0 : ‖g - k‖ = 0
    · rw [h0]; exact norm_nonneg _
    · have hpos : 0 < ‖g - k‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  have h5 : ‖F x - F p‖ ≤ β * t * ‖g‖ := by
    have := hFL x p
    rw [hxp, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at this
    linarith
  have h6 : ‖g - k‖ ≤ β * t * ‖g‖ := h4.trans h5
  have e1 : k = g - (g - k) := by abel
  have e2 : g = k + (g - k) := by abel
  constructor
  · have : ‖g‖ ≤ ‖k‖ + ‖g - k‖ := by
      calc ‖g‖ = ‖k + (g - k)‖ := by rw [← e2]
        _ ≤ _ := norm_add_le _ _
    nlinarith
  · have : ‖k‖ ≤ ‖g‖ + ‖g - k‖ := by
      calc ‖k‖ = ‖g - (g - k)‖ := by rw [← e1]
        _ ≤ _ := norm_sub_le _ _
    nlinarith
