-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.apply_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:40.235804+00:00
-- url     : https://prove2.me/submissions/ea179387-8747-4c0c-b14e-81330b2e4590

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
    (hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u)) {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w)
    (g : G) (u : H) :
    ρ g (∫ x, w x • ρ x u ∂μ) = ∫ x, w (g⁻¹ * x) • ρ x u ∂μ := by
  rw [← (ρ g).integral_comp_comm (integrable_w μ ρ hρ hw hc u),
    ← integral_mul_left_eq_self (fun x => w (g⁻¹ * x) • ρ x u) g]
  congr 1
  funext x
  rw [inv_mul_cancel_left, hmul, ContinuousLinearMap.map_smul_of_tower]
end CompanionTheory.D.gk.admitted.Gard
