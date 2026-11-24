-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.valuation_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:59:03.941167+00:00
-- url     : https://prove2.me/submissions/c182daad-5fbd-4d02-b35c-ff1538a610c1

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
namespace Formalism.PairingDivisionLocalBalance
theorem _root_.solution : ValAdd := by
  unfold ValAdd
  intro K _ _ _ w a b ha hb hab
  exact vw_add w a b ha hb hab
end Formalism.PairingDivisionLocalBalance
