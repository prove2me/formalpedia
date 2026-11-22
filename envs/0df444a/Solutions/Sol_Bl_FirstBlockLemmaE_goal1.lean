-- Prove2me | solution 1 for Bl.FirstBlockLemmaE.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:08:51.805372+00:00
-- url     : https://prove2.me/submissions/4a8a41bb-d85c-41fd-b4e7-f152fa4e9435

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaE
namespace Bl.FirstBlockLemmaE
theorem _root_.solution :
  ∀ {L : Type} [inst : Field.{0} L] [NumberField.{0} L] (x : L) (c : Int),
  Eq.{1} (HPow.hPow.{0, 0, 0} x 2) (HAdd.hAdd.{0, 0, 0} x (Int.cast.{0} c)) →
    Exists.{1} fun (X : NumberField.RingOfIntegers.{0} L) ↦
      And (Eq.{1} (NumberField.RingOfIntegers.val.{0} X) x)
        (Eq.{1} (HPow.hPow.{0, 0, 0} X 2) (HAdd.hAdd.{0, 0, 0} X (Int.cast.{0} c))) := by
  intro L _ _ x c h
  have hi : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, h]
      simp
  refine ⟨⟨x, hi⟩, rfl, ?_⟩
  apply NumberField.RingOfIntegers.coe_injective
  exact h
end Bl.FirstBlockLemmaE
