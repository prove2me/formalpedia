-- Prove2me | solution 1 for Formalism.REAL.indefinite_unitary_unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:59:33.221647+00:00
-- url     : https://prove2.me/submissions/0b145e26-b45b-4ccc-a4c5-09f983252bec

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Theorems.Thm_Formalism_REAL_map_mul_right_haar_modular_alt
import Theorems.Thm_Formalism_REAL_modularCharacter_eq_one_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped NNReal ENNReal
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : Unimodular := by
  intro n ε g
  rw [map_mul_right_haar_modular_alt, modularCharacter_eq_one_alt, one_smul]
end Formalism.REAL
