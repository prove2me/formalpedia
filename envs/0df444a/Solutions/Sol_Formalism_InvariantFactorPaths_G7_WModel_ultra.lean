-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.ultra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:45:57.160901+00:00
-- url     : https://prove2.me/submissions/dea052bd-7e07-48d6-a5f9-222173c3b6d8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_nonarch

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
attribute [local instance] nf
namespace Formalism.InvariantFactorPaths.G7.WModel
theorem _root_.solution : IsUltrametricDist (KK p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => abv_nonarch p x y
end Formalism.InvariantFactorPaths.G7.WModel
