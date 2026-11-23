-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.PrismTransfer.integrable_of_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:52.949084+00:00
-- url     : https://prove2.me/submissions/e577dadc-3bc5-42eb-a52d-58946831361e

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Kronecker Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.PrismTransfer
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
  (e : K → ℂ)
variable {μ e}
omit [IsTopologicalGroup G]
namespace CompanionTheory.D.gk.admitted.PrismTransfer
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [SecondCountableTopology K] {f : K → V}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
end CompanionTheory.D.gk.admitted.PrismTransfer
