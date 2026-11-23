-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ProductFactorBounds.letter_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:11.697461+00:00
-- url     : https://prove2.me/submissions/f8956d37-f1a9-4c28-b354-3874b547ef75

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ProductFactorBounds
open Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.ProductFactorBounds
theorem _root_.solution {K : Type} [Field K] (l : WLetter K) (Y : K) (h : OffPoles l Y) :
    (if l.plus then (Y - l.pt + 1) / (Y - l.pt) else (l.pt - Y) / (l.pt - Y - 1)) /
      (if l.first then
        (if l.plus then (Y + 1 - l.pt) / (Y + 1 - l.pt - 1)
          else (l.pt - (Y + 1)) / (l.pt - (Y + 1) - 1)) else 1) = wFactor l Y := by
  obtain ⟨p, t, f⟩ := l
  cases p <;> cases f
  · simp [wFactor]
  · have h' : t - Y ≠ 1 ∧ t - Y ≠ 2 := by simpa [OffPoles] using h
    have h1 : t - Y - 1 ≠ 0 := sub_ne_zero.2 h'.1
    have h2 : t - (Y + 1) ≠ 0 := by
      intro e; apply h1; rw [← e]; ring
    have h3 : t - (Y + 1) - 1 ≠ 0 := by
      intro e; apply h'.2; linear_combination e
    simp only [wFactor, if_true, Bool.false_eq_true, if_false]
    field_simp
    ring
  · simp [wFactor]
  · have h' : Y - t ≠ 0 ∧ Y - t ≠ -1 := by simpa [OffPoles] using h
    have h1 : Y - t + 1 ≠ 0 := by
      intro e; apply h'.2; linear_combination e
    have h4 : Y - t ≠ 0 := h'.1
    simp only [wFactor, if_true]
    have e1 : Y + 1 - t = Y - t + 1 := by ring
    have e2 : Y + 1 - t - 1 = Y - t := by ring
    rw [e2, e1]
    exact div_self (div_ne_zero h1 h4)
end Formalism.FourierDecayAlt.P.ProductFactorBounds
