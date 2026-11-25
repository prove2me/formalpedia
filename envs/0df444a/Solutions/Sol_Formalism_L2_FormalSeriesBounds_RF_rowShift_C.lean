-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.rowShift_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:42.639369+00:00
-- url     : https://prove2.me/submissions/f2b64d63-a3e4-4580-83aa-c2eef1671bc3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (σ : T) (i i' : Fin (r σ)) (t z : C) :
    rowShift r n C σ i i' t (MvPolynomial.C z) = MvPolynomial.C z := (rowShift r n C σ i i' t).commutes z
end Formalism.L2.FormalSeriesBounds.RF
