-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.norm_eI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:24.223929+00:00
-- url     : https://prove2.me/submissions/3e490795-0df7-4e1d-851d-3d76c6fc78d5

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_IntegrableMulBc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Filter BoundedContinuousFunction
open scoped ENNReal
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
namespace CompanionTheory.D.gk.RF
theorem _root_.solution (r : ℝ) : ‖eI r‖ = 1 := Complex.norm_exp_ofReal_mul_I r
end CompanionTheory.D.gk.RF
