-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.GeV.mul0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:34.324858+00:00
-- url     : https://prove2.me/submissions/b9db4f5b-3812-4f87-a360-d2b2578be8a0

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_GeV_mul

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
theorem _root_.solution {w : Pl K} {x y : K} (hx : GeV w 0 x) (hy : GeV w 0 y) : GeV w 0 (x * y) := by
  have h := GeV.mul hx hy
  rwa [add_zero] at h
end GeV
end Formalism.PairingDivisionLocalBalance
