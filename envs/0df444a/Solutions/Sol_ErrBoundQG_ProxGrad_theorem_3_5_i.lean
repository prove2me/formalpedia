-- Prove2me | solution 1 for ErrBoundQG.ProxGrad.theorem_3_5_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:08:03.105142+00:00
-- url     : https://prove2.me/submissions/fc83eda9-a1b2-4796-8411-eed290d6d148

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
    (hJG : ThreeOpSplitting.Convergence.IsResolvent t G JG) :
    ∀ x, ∀ v ∈ Φ x, ‖t⁻¹ • (x - JG (x - t • F x))‖ ≤ ‖v‖ := by
  intro x v hv
  rw [hF x] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  set p := JG (x - t • F x) with hp
  set g : EuclideanSpace ℝ (Fin n) := t⁻¹ • (x - p) with hg
  have ht0 : t ≠ 0 := ht.ne'
  have hu : t⁻¹ • ((x - t • F x) - p) ∈ G p := hJG (x - t • F x)
  have hu' : t⁻¹ • ((x - t • F x) - p) = g - F x := by
    have : x - t • F x - p = (x - p) - t • F x := by abel
    rw [hg, this, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [hu'] at hu
  have hmon := hG.1 p x _ _ hu hw
  have hpx : p - x = -(t • g) := by
    rw [hg, smul_smul, mul_inv_cancel₀ ht0, one_smul]; abel
  rw [hpx] at hmon
  have h1 : inner ℝ (-(t • g)) (g - F x - w) = -t * inner ℝ g (g - (F x + w)) := by
    rw [inner_neg_left, real_inner_smul_left]
    have : g - F x - w = g - (F x + w) := by abel
    rw [this]; ring
  rw [h1] at hmon
  have h2 : inner ℝ g g ≤ inner ℝ g (F x + w) := by
    have : inner ℝ g (g - (F x + w)) ≤ 0 := by nlinarith
    rw [inner_sub_right] at this
    linarith
  rw [real_inner_self_eq_norm_sq] at h2
  have h3 := real_inner_le_norm g (F x + w)
  by_cases h0 : ‖g‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith
