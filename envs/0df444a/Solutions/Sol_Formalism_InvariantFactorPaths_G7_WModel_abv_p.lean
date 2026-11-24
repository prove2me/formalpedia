-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.abv_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:53:23.486609+00:00
-- url     : https://prove2.me/submissions/1ff4d0bd-c3fe-442d-93d1-a207da086e97

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_maxIdeal_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_toNNReal_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.WModel
variable (p : ℕ) [hp : Fact p.Prime]
namespace Formalism.InvariantFactorPaths.G7.WModel
theorem _root_.solution : abv p (p : KK p) = (p : ℝ)⁻¹ := by
  have h : (p : KK p) = algebraMap (WW p) (KK p) (p : WW p) := by simp
  rw [h, abv, adicAbv_of_algebraMap]
  have h2 := intValuation_singleton (IsDiscreteValuationRing.maximalIdeal (WW p))
    (WittVector.p_nonzero p _) (maxIdeal_eq p)
  simp only [intAdicAbv, intAdicAbvDef, AbsoluteValue.coe_mk, MulHom.coe_mk, h2]
  rw [toNNReal_exp]
  simp
end Formalism.InvariantFactorPaths.G7.WModel
