-- Prove2me | solution 1 for DeletionCode.FiniteConflictGraph.nonexceptional_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:35:00.306584+00:00
-- url     : https://prove2.me/submissions/28067500-bab9-43ee-8a65-25f9f2838d2c

import Definitions.Def_DeletionCode_AlignmentTrace
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Mathlib.Combinatorics.SimpleGraph.Basic
import Definitions.Def_DeletionCode_FiniteConflictGraph
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans


set_option autoImplicit true
open DeletionCode DeletionCode.FiniteConflictGraph
open HeaderRecovery AlignmentTrace EditAlignment
variable {n : ℕ} {H : Type*}
namespace DeletionCode.FiniteConflictGraph
theorem _root_.solution {t k : ℕ} {label : Bits n → H}
    (x : Vertex t k label) (y : Bits n)
    (hxy : x.val ≠ y) (hlabel : label x.val = label y)
    (d : ℕ) (trace : Trace) (hd : d ≤ t)
    (hsource : trace.source = List.ofFn x.val)
    (htarget : trace.target = List.ofFn y)
    (hdel : trace.deletions = d) (hins : trace.insertions = d) :
    trace.deletions = t ∧ trace.insertions = t ∧
      Separated (4 * windowLength k) trace := by
  have hsmall : ¬ d < t := by
    intro hlt
    exact x.property.2 ⟨x.property.1, y, hxy, hlabel, d, trace,
      hsource, htarget, hdel, hins, Or.inl hlt⟩
  have hdt : d = t := by omega
  have hsep : Separated (4 * windowLength k) trace := by
    by_contra hnot
    exact x.property.2 ⟨x.property.1, y, hxy, hlabel, d, trace,
      hsource, htarget, hdel, hins, Or.inr ⟨hdt, hnot⟩⟩
  exact ⟨hdel.trans hdt, hins.trans hdt, hsep⟩
end DeletionCode.FiniteConflictGraph
