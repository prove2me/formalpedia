-- Prove2me | solution 1 for DeletionCode.RecordPacking.unpack_of_positions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:59:54.625635+00:00
-- url     : https://prove2.me/submissions/e24b57ad-a998-49b7-9eb6-371e8d212159

import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_RecordPacking

set_option autoImplicit true
open DeletionCode DeletionCode.RecordPacking
variable {α β : Type*}
namespace DeletionCode.RecordPacking
theorem _root_.solution (decode : β → Option (Option α)) (size : ℕ)
    (rows : Fin size → β) (xs : List α) (hsize : xs.length ≤ size)
    (hrows : ∀ i, decode (rows i) = some xs[i.val]?) :
    unpack decode size rows = some xs := by
  induction size generalizing xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    rfl
  | succ size ih =>
    cases xs with
    | nil =>
      have hfirst := hrows ⟨0, by omega⟩
      change decode (rows 0) = some none at hfirst
      have hrest : ∀ i : Fin size, decode (rows i.succ) = some ([] : List α)[i.val]? := by
        intro i
        simpa using hrows i.succ
      have hr := ih (fun i => rows i.succ) [] (by simp) hrest
      simp [unpack, hfirst, hr]
    | cons a xs =>
      have hfirst := hrows ⟨0, by omega⟩
      change decode (rows 0) = some (some a) at hfirst
      have hrest : ∀ i : Fin size, decode (rows i.succ) = some xs[i.val]? := by
        intro i
        simpa using hrows i.succ
      have hr := ih (fun i => rows i.succ) xs (by simp at hsize; omega) hrest
      simp [unpack, hfirst, hr]
end DeletionCode.RecordPacking
