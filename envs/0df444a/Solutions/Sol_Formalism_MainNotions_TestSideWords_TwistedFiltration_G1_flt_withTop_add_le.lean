-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_withTop_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:08:29.965743+00:00
-- url     : https://prove2.me/submissions/54560dab-0612-4fdb-81ab-5ba3beaf2f7a

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
theorem _root_.solution {a b c : WithTop ℤ}
    (h : ∀ t u : ℤ, (t : WithTop ℤ) ≤ a → (u : WithTop ℤ) ≤ b → ((t + u : ℤ) : WithTop ℤ) ≤ c) : a + b ≤ c := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction c using WithTop.recTopCoe with
    | top => exact le_top
    | coe z =>
      exfalso
      induction b using WithTop.recTopCoe with
      | top =>
        have := WithTop.coe_le_coe.1 (h (z + 1) 0 le_top le_top)
        linarith
      | coe y =>
        have := WithTop.coe_le_coe.1 (h (z - y + 1) y le_top le_rfl)
        linarith
  | coe x =>
    induction b using WithTop.recTopCoe with
    | top =>
      induction c using WithTop.recTopCoe with
      | top => exact le_top
      | coe z =>
        exfalso
        have := WithTop.coe_le_coe.1 (h x (z - x + 1) le_rfl le_top)
        linarith
    | coe y =>
      rw [← WithTop.coe_add]
      exact h x y le_rfl le_rfl
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
