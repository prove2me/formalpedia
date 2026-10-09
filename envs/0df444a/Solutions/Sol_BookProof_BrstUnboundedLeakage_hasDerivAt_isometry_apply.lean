-- Prove2me | solution 1 for BookProof.BrstUnboundedLeakage.hasDerivAt_isometry_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:46:34.097402+00:00
-- url     : https://prove2.me/submissions/595c42da-ef92-4a3d-94a3-2628075e5054

-- Generated from ChapterBrstUnboundedLeakage.lean — solution of BookProof.BrstUnboundedLeakage.hasDerivAt_isometry_apply
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
open BookProof.BrstUnboundedLeakage



open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution {U : ℝ → H →L[ℂ] H} {f : ℝ → H} {f' : H}
    (hiso : ∀ (h : ℝ) (y : H), ‖U h y‖ = ‖y‖) (hU0 : ∀ y : H, U 0 y = y)
    (hcont : ∀ y : H, Tendsto (fun h : ℝ => U h y) (𝓝 0) (𝓝 y))
    (hf : HasDerivAt f f' 0) (hf0 : f 0 = 0) :
    HasDerivAt (fun h : ℝ => U h (f h)) f' 0 := by

  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hc2 : 0 < c / 2 := by linarith
  -- the curve's own error term
  have h1 : ∀ᶠ h : ℝ in 𝓝 0, ‖f (0 + h) - f 0 - h • f'‖ ≤ (c / 2) * ‖h‖ := by
    have := (hasDerivAt_iff_isLittleO_nhds_zero.mp hf)
    exact (Asymptotics.isLittleO_iff.mp this) hc2
  -- the strong-continuity error term
  have h2 : ∀ᶠ h : ℝ in 𝓝 0, ‖U h f' - f'‖ ≤ c / 2 := by
    have hten := hcont f'
    have : ∀ᶠ h : ℝ in 𝓝 0, U h f' ∈ Metric.closedBall f' (c / 2) :=
      hten (Metric.closedBall_mem_nhds f' hc2)
    filter_upwards [this] with h hh
    simpa [Metric.mem_closedBall, dist_eq_norm] using hh
  filter_upwards [h1, h2] with h hh1 hh2
  rw [zero_add] at hh1
  simp only [zero_add]
  have hsplit : U h (f h) - U 0 (f 0) - h • f'
      = U h (f h - f 0 - h • f') + h • (U h f' - f') := by
    have hU0f : U 0 (f 0) = 0 := by rw [hU0, hf0]
    have hlin : U h (f h - f 0 - h • f') = U h (f h) - U h (f 0) - h • U h f' := by
      simp [map_sub, ContinuousLinearMap.map_smul_of_tower]
    rw [hlin, hU0f, hf0]
    simp only [map_zero, smul_sub]
    abel
  rw [hsplit]
  have hb1 : ‖U h (f h - f 0 - h • f')‖ ≤ (c / 2) * ‖h‖ := by
    rw [hiso]; exact hh1
  have hb2 : ‖h • (U h f' - f')‖ ≤ ‖h‖ * (c / 2) := by
    rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hh2 (norm_nonneg _)
  calc ‖U h (f h - f 0 - h • f') + h • (U h f' - f')‖
      ≤ ‖U h (f h - f 0 - h • f')‖ + ‖h • (U h f' - f')‖ := norm_add_le _ _
    _ ≤ (c / 2) * ‖h‖ + ‖h‖ * (c / 2) := add_le_add hb1 hb2
    _ = c * ‖h‖ := by ring
    _ = c * ‖(id : ℝ → ℝ) h‖ := rfl
