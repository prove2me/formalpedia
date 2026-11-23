-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.norm_eI_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:22.783928+00:00
-- url     : https://prove2.me/submissions/1e5f7f15-5a6b-46bf-a108-54c2aa09b334

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_IntegrableMulBc
import Theorems.Thm_CompanionTheory_D_gk_RF_norm_eI
import Theorems.Thm_CompanionTheory_D_gk_RF_eI_add

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
theorem _root_.solution (r r' : ℝ) : ‖eI r - eI r'‖ ≤ min 2 |r - r'| := by
  refine le_min ((norm_sub_le _ _).trans (by rw [norm_eI, norm_eI]; norm_num)) ?_
  have : eI r - eI r' = (eI (r - r') - 1) * eI r' := by rw [sub_mul, ← eI_add, sub_add_cancel, one_mul]
  rw [this, norm_mul, norm_eI, mul_one, eI, mul_comm]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le
end CompanionTheory.D.gk.RF
