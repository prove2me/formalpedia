-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.comm_U_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:52:46.257531+00:00
-- url     : https://prove2.me/submissions/0bd1afcf-c416-41be-b6c9-1a16c207bd8a

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_comm_U

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution (c : kˣ) (ψ : (Fin r → k) → R) (f : Fin r → k) :
    opU (diaV c ψ) f = diaP c (opU ψ) f := congrFun (comm_U c ψ) f
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
