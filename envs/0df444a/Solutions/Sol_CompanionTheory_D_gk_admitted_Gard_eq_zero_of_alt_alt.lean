-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.eq_zero_of_alt_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:43.051958+00:00
-- url     : https://prove2.me/submissions/e2e80ba9-6a15-4796-b354-5b1575cca101

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_integrable_w

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) (h0 : 0 ≤ w) (h1 : w 1 ≠ 0)
    (y : H) (hy : ∀ x, w x ≠ 0 → ‖ρ x y - y‖ ≤ 1 / 2 * ‖y‖) (hT : ∫ x, w x • ρ x y ∂μ = 0) : y = 0 := by
  have hpos := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hc h0 h1
  have hwi : Integrable w μ := hw.integrable_of_hasCompactSupport hc
  have e : ∫ x, w x • (ρ x y - y) ∂μ = -((∫ x, w x ∂μ) • y) := by
    simp only [smul_sub]
    rw [integral_sub (integrable_w μ ρ hρ hw hc y) (hwi.smul_const y), hT, integral_smul_const, zero_sub]
  have b : ‖∫ x, w x • (ρ x y - y) ∂μ‖ ≤ ∫ x, w x * (1 / 2 * ‖y‖) ∂μ := by
    refine norm_integral_le_of_norm_le (hwi.mul_const _) (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_of_nonneg (h0 x)]
    by_cases hx : w x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_left (hy x hx) (h0 x)
  rw [e, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at b
  have := le_of_mul_le_mul_left b hpos
  have h2 : ‖y‖ = 0 := by linarith [norm_nonneg y]
  exact norm_eq_zero.1 h2
end CompanionTheory.D.gk.admitted.Gard
