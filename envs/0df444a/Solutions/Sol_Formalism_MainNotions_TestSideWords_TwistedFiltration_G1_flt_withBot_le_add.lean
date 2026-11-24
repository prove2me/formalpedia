-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_withBot_le_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:08:28.2921+00:00
-- url     : https://prove2.me/submissions/3fac4907-cf43-4095-a69e-4971a2380332

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
theorem _root_.solution {a b c : WithBot ℤ}
    (h : ∀ t u : ℤ, a ≤ (t : WithBot ℤ) → b ≤ (u : WithBot ℤ) → c ≤ ((t + u : ℤ) : WithBot ℤ)) : c ≤ a + b := by
  induction c using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe z =>
    induction a using WithBot.recBotCoe with
    | bot =>
      exfalso
      induction b using WithBot.recBotCoe with
      | bot =>
        have := WithBot.coe_le_coe.1 (h (z - 1) 0 bot_le bot_le)
        linarith
      | coe y =>
        have := WithBot.coe_le_coe.1 (h (z - y - 1) y bot_le le_rfl)
        linarith
    | coe x =>
      induction b using WithBot.recBotCoe with
      | bot =>
        exfalso
        have := WithBot.coe_le_coe.1 (h x (z - x - 1) le_rfl bot_le)
        linarith
      | coe y =>
        rw [← WithBot.coe_add]
        exact h x y le_rfl le_rfl
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
