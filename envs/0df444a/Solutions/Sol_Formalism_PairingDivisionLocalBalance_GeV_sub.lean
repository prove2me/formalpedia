-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.GeV.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:14:39.335211+00:00
-- url     : https://prove2.me/submissions/52490275-8da4-48a7-9620-0b322a0e8629

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_GeV_add
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_GeV_mul0
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_GeV_negOne

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
theorem _root_.solution {w : Pl K} {x y : K} (hx : GeV w 0 x) (hy : GeV w 0 y) : GeV w 0 (x - y) := by
  rw [sub_eq_add_neg, neg_eq_neg_one_mul]
  exact GeV.add hx (GeV.mul0 (GeV.negOne w) hy)
end GeV
end Formalism.PairingDivisionLocalBalance
