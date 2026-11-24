-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.maxIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:45:53.537218+00:00
-- url     : https://prove2.me/submissions/84854e03-1303-488b-abdb-237a0749f8ad

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
theorem _root_.solution : (IsDiscreteValuationRing.maximalIdeal (WW p)).asIdeal =
    Ideal.span {(p : WW p)} :=
  (WittVector.irreducible p).maximalIdeal_eq
end Formalism.InvariantFactorPaths.G7.WModel
