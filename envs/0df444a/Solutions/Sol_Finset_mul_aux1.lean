-- Prove2me | solution 1 for Finset.mul_aux1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:27.052666+00:00
-- url     : https://prove2.me/submissions/849b3bd5-eebd-4ebe-950e-ebad9f27997b

module
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Definitions.Def_Erdos338_Kneser_Kneser

set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}
open Finset
namespace Finset
theorem _root_.solution
    (ih : #(s' * (s' * t').mulStab) + #(t' * (s' * t').mulStab) ≤ #(s' * t') + #(s' * t').mulStab)
    (hconv : #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab)
    (hnotconv :
      #(C ∪ s' * t') + #(C ∪ s' * t').mulStab < #(s ∩ t) + #((s ∪ t) * (C ∪ s' * t').mulStab))
    (hCun : (C ∪ s' * t').mulStab = (s' * t').mulStab) (hdisj : Disjoint C (s' * t')) :
    (#((s ∪ t) * C.mulStab) - #((s ∪ t) * (s' * t').mulStab) : ℤ) <
      #C.mulStab - #(s' * (s' * t').mulStab) - #(t' * (s' * t').mulStab) := by
  set H := C.mulStab
  set H' := (s' * t').mulStab
  set C' := C ∪ s' * t'
  zify at hconv hnotconv ih
  calc
    (#((s ∪ t) * H) - #((s ∪ t) * H') : ℤ) < #C + #H - #(s ∩ t) - (#C' + #H' - #(s ∩ t)) := by
      rw [← hCun]
      linarith [hconv, hnotconv]
    _ = #H - #(s' * t') - #H' := by
      rw [card_union_of_disjoint hdisj, Int.natCast_add]
      abel
    _ ≤ #H - #(s' * H') - #(t' * H') := by linarith [ih]
end Finset
