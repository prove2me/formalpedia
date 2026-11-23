-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.reprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:25.414575+00:00
-- url     : https://prove2.me/submissions/5ec13817-f4b6-43aa-8e8e-29e5ea18c701

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_IntegrableMulBc
import Theorems.Thm_Bl_FirstLemmaL_goal1


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
theorem _root_.solution {φ : G → ℂ} (hφ : Integrable φ μ) (hi : ∀ w, ∫ y, φ y * φ (y⁻¹ * w) ∂μ = φ w) {F : G → ℂ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ y, ‖F y‖ ≤ M) :
    ∫ y, φ y * ∫ z, φ z * F (y * z) ∂μ ∂μ = ∫ w, φ w * F w ∂μ :=
  _root_.Bl.FirstLemmaL.goal1 hφ hi hF hM
end CompanionTheory.D.gk.RF
