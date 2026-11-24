-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.abv_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:58.930539+00:00
-- url     : https://prove2.me/submissions/5fc549ab-d828-4c2d-9dba-667c8b4b6bf6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel

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
theorem _root_.solution (u : (WW p)ˣ) : abv p (algebraMap (WW p) (KK p) (u : WW p)) = 1 := by
  refine (adicAbv_coe_eq_one_iff _ _ _).2 ?_
  show (u : WW p) ∉ IsLocalRing.maximalIdeal _
  simp
end Formalism.InvariantFactorPaths.G7.WModel
