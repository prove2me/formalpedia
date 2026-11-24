-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.card_dirichletCharacter_eq_totient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:44:08.592851+00:00
-- url     : https://prove2.me/submissions/5d624ae1-a2cd-438a-a49b-1dc0d4d6fd30

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (q : ℕ) [NeZero q] :
    ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = (q.totient : ℝ) := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
end Formalism.ZeroFreeDirichlet
