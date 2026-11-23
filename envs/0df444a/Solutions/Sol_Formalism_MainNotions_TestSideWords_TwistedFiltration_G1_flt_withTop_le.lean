-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_withTop_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:50.076521+00:00
-- url     : https://prove2.me/submissions/832e539f-d312-4568-bf15-375126349397

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
theorem _root_.solution {a b : WithTop ℤ} {N : ℤ}
    (h : ∀ t : ℤ, (t : WithTop ℤ) ≤ a → ((t - N : ℤ) : WithTop ℤ) ≤ b) : a ≤ b + (N : WithTop ℤ) := by
  induction a using WithTop.recTopCoe with
  | top =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe c =>
      exfalso
      have := WithTop.coe_le_coe.1 (h (c + N + 1) le_top)
      linarith
  | coe x =>
    have h1 := h x le_rfl
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe c =>
      have := WithTop.coe_le_coe.1 h1
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      linarith
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
