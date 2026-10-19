-- Prove2me | solution 1 for GapCVP.CL.transitionClause_satisfied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/9c077f5a-bb52-47e2-9bf0-3ef3bed53ab4

import Mathlib
import Definitions.Def_GapCVP

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.CL
namespace GapCVP.CL
theorem _root_.solution {T S : ℕ}
    (spec : Specification T S)
    (trace : Time T → Position T → Symbol S)
    (htransition : ∀ w : Window T,
      spec.allowed
        (trace w.1.1 (leftPosition w),
         trace w.1.1 w.1.2,
         trace w.1.1 (rightPosition w),
         trace (nextTime w) w.1.2) = true)
    (w : Window T) (symbols : WindowSymbols S)
    (hforbidden : spec.allowed symbols = false) :
    satisfiesClause (assignmentOfTrace trace) (transitionClause w symbols) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  by_cases h₁ : trace w.1.1 (leftPosition w) = symbols.1
  · by_cases h₂ : trace w.1.1 w.1.2 = symbols.2.1
    · by_cases h₃ : trace w.1.1 (rightPosition w) = symbols.2.2.1
      · have h₄ : trace (nextTime w) w.1.2 ≠ symbols.2.2.2 := by
          intro h₄
          have hgood := htransition w
          rw [h₁, h₂, h₃, h₄, hforbidden] at hgood
          contradiction
        refine ⟨negative (nextTime w, w.1.2, symbols.2.2.2),
          by simp [transitionClause], ?_⟩
        simp [negative, assignmentOfTrace, h₄]
      · refine ⟨negative (w.1.1, rightPosition w, symbols.2.2.1),
          by simp [transitionClause], ?_⟩
        simp [negative, assignmentOfTrace, h₃]
    · refine ⟨negative (w.1.1, w.1.2, symbols.2.1),
        by simp [transitionClause], ?_⟩
      simp [negative, assignmentOfTrace, h₂]
  · refine ⟨negative (w.1.1, leftPosition w, symbols.1),
      by simp [transitionClause], ?_⟩
    simp [negative, assignmentOfTrace, h₁]
end GapCVP.CL
