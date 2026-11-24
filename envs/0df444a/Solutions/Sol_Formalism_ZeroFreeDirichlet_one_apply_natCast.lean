-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.one_apply_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:50.049812+00:00
-- url     : https://prove2.me/submissions/f4aadfe7-ae92-4b3b-be39-166eefc24779

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} (n : ℕ) :
    (1 : DirichletCharacter ℂ q) (n : ZMod q) = if n.Coprime q then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).2 h)
  · exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n q).1 hu))
end Formalism.ZeroFreeDirichlet
