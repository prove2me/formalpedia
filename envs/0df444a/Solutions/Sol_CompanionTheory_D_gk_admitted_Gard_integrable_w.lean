-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.integrable_w
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:09:42.361145+00:00
-- url     : https://prove2.me/submissions/9e739818-b709-4ad4-b175-6f423d588c0e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg

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
theorem _root_.solution (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) {w : G → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) (u : H) : Integrable (fun x => w x • ρ x u) μ :=
  (hw.smul (hρ u)).integrable_of_hasCompactSupport hc.smul_right
end CompanionTheory.D.gk.admitted.Gard
