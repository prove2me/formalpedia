-- Prove2me | solution 1 for FiniteEnergyPlane.injOn_ball_of_hasStrictFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T15:47:36.817146+00:00
-- url     : https://prove2.me/submissions/fe90df1f-f5a4-4a3c-a445-c353d402eff4

import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem injOn_ball_of_hasStrictFDerivAt_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F}
    {x : E} (hf : HasStrictFDerivAt f f' x) (hi : Function.Injective f') :
    ∃ δ > 0, Set.InjOn f (Metric.ball x δ) := by
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith (𝕜 := ℝ) (f' : E →ₗ[ℝ] F)
    (LinearMap.ker_eq_bot.mpr hi)
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hlow : ∀ v : E, ‖v‖ ≤ K * ‖f' v‖ := by
    intro v
    have := hanti.le_mul_dist v 0
    simpa [dist_zero_right] using this
  have hc : (0 : ℝ) < 1 / (2 * K) := by positivity
  have hev := (hasStrictFDerivAt_iff_isLittleO.mp hf).def hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨δ, hδ, fun a ha b hb hab => ?_⟩
  have hmem : ((a, b) : E × E) ∈ Metric.ball ((x, x) : E × E) δ := by
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp ha) (Metric.mem_ball.mp hb)
  have h1 := hball _ hmem
  simp only [hab, sub_self, zero_sub, norm_neg] at h1
  have h2 := hlow (a - b)
  have h3 : K * ‖f' (a - b)‖ ≤ K * (1 / (2 * K) * ‖a - b‖) :=
    mul_le_mul_of_nonneg_left h1 hK'.le
  have h4 : K * (1 / (2 * K) * ‖a - b‖) = ‖a - b‖ / 2 := by
    field_simp
  have h5 : ‖a - b‖ ≤ 0 := by
    have := norm_nonneg (a - b)
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h5)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {f' : E →L[ℝ] F}
    {x : E} (hf : HasStrictFDerivAt f f' x) (hi : Function.Injective f') :
    ∃ δ > 0, Set.InjOn f (Metric.ball x δ) :=
  injOn_ball_of_hasStrictFDerivAt_aux hf hi
