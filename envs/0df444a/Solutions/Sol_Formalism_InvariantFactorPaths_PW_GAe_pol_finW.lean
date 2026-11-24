-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.GAe_pol_finW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:25.605062+00:00
-- url     : https://prove2.me/submissions/bd258314-23ad-4ccb-a6c9-b9ee7656d393

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL L2 : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) :
    (GAe p LL j e).FinW (Pol p r L2) := by
  classical
  refine ⟨(pol_finite (r := r) L2).toFinset.image (Finsupp.weight (fun x => (wv LL j x) ∘ e)),
    fun x hx μ hμ => ?_⟩
  show weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) μ x = 0
  apply weightedHomogeneousComponent_eq_zero'
  intro d hd h
  apply hμ
  rw [Finset.mem_image]
  refine ⟨d, ?_, h⟩
  rw [Set.Finite.mem_toFinset]
  exact (MvPolynomial.mem_restrictSupport_iff ℚ_[p]).mp hx hd
end Formalism.InvariantFactorPaths.PW
