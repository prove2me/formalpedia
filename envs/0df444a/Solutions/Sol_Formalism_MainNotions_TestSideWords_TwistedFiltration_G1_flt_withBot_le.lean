-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_withBot_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:08:27.457345+00:00
-- url     : https://prove2.me/submissions/9e4c64eb-4696-45eb-9105-4110c299cffa

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution {a b : WithBot ℤ} {N : ℤ}
    (h : ∀ M : ℤ, b ≤ (M : WithBot ℤ) → a ≤ ((M + N : ℤ) : WithBot ℤ)) : a ≤ b + (N : WithBot ℤ) := by
  induction b using WithBot.recBotCoe with
  | bot =>
    induction a using WithBot.recBotCoe with
    | bot => simp
    | coe x =>
      exfalso
      have := WithBot.coe_le_coe.1 (h (x - N - 1) bot_le)
      linarith
  | coe c =>
    have := h c le_rfl
    rwa [← WithBot.coe_add]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
