-- Prove2me | solution 1 for GapCVP.CL.traceOfAssignment_transition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/6de8b489-dcec-49c4-9e74-356c877f0169

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CL_traceOfAssignment_selected

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
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec))
    (w : Window T) :
    spec.allowed
      (traceOfAssignment spec assignment hsat w.1.1 (leftPosition w),
       traceOfAssignment spec assignment hsat w.1.1 w.1.2,
       traceOfAssignment spec assignment hsat w.1.1 (rightPosition w),
       traceOfAssignment spec assignment hsat (nextTime w) w.1.2) = true := by
  have hsat' := hsat
  simp only [GapCVP.CL.satisfiesFormula, GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsat'
  let symbols : WindowSymbols S :=
    (traceOfAssignment spec assignment hsat w.1.1 (leftPosition w),
     traceOfAssignment spec assignment hsat w.1.1 w.1.2,
     traceOfAssignment spec assignment hsat w.1.1 (rightPosition w),
     traceOfAssignment spec assignment hsat (nextTime w) w.1.2)
  change spec.allowed symbols = true
  cases hallowed : spec.allowed symbols with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨literal, hliteral, hvalue⟩ :=
      hsat' (transitionClause w symbols)
        (transitionClause_mem_tableauFormula spec w symbols hallowed)
    simp only [transitionClause, Finset.mem_insert,
      Finset.mem_singleton] at hliteral
    rcases hliteral with h₁ | h₂ | h₃ | h₄
    · subst literal
      have hfalse : assignment
          (w.1.1, leftPosition w, symbols.1) = false := by
        simpa [negative] using hvalue
      have htrue := traceOfAssignment_selected spec assignment hsat
        w.1.1 (leftPosition w)
      change assignment
        (w.1.1, leftPosition w,
          traceOfAssignment spec assignment hsat w.1.1 (leftPosition w))
          = false at hfalse
      simp [htrue] at hfalse
    · subst literal
      have hfalse : assignment (w.1.1, w.1.2, symbols.2.1) = false := by
        simpa [negative] using hvalue
      have htrue := traceOfAssignment_selected spec assignment hsat
        w.1.1 w.1.2
      change assignment
        (w.1.1, w.1.2,
          traceOfAssignment spec assignment hsat w.1.1 w.1.2)
          = false at hfalse
      simp [htrue] at hfalse
    · subst literal
      have hfalse : assignment
          (w.1.1, rightPosition w, symbols.2.2.1) = false := by
        simpa [negative] using hvalue
      have htrue := traceOfAssignment_selected spec assignment hsat
        w.1.1 (rightPosition w)
      change assignment
        (w.1.1, rightPosition w,
          traceOfAssignment spec assignment hsat w.1.1 (rightPosition w))
          = false at hfalse
      simp [htrue] at hfalse
    · subst literal
      have hfalse : assignment
          (nextTime w, w.1.2, symbols.2.2.2) = false := by
        simpa [negative] using hvalue
      have htrue := traceOfAssignment_selected spec assignment hsat
        (nextTime w) w.1.2
      change assignment
        (nextTime w, w.1.2,
          traceOfAssignment spec assignment hsat (nextTime w) w.1.2)
          = false at hfalse
      simp [htrue] at hfalse
end GapCVP.CL
