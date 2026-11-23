-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.GeV.of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:18.859287+00:00
-- url     : https://prove2.me/submissions/57de4289-cf4d-4703-9670-a356f71db43f

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.PairingDivisionLocalBalance
namespace GeV
theorem _root_.solution {w : Pl K} {x : K} (h : vw w x = 0) : GeV w 0 x := by
  unfold GeV
  right
  rw [h]
  simp
end GeV
end Formalism.PairingDivisionLocalBalance
