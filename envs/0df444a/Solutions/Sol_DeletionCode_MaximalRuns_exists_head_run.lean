-- Prove2me | solution 1 for DeletionCode.MaximalRuns.exists_head_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:02.390814+00:00
-- url     : https://prove2.me/submissions/7a9b6ddc-479f-47ed-9e60-696107342d52

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
section
namespace DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
private theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all
end DeletionCode.MaximalRuns
end

set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns
namespace DeletionCode.MaximalRuns
theorem _root_.solution (bit : Bool) (tail : List Bool) :
    ∃ (rho : ℕ) (suffix : List Bool), 0 < rho ∧
      bit :: tail = List.replicate rho bit ++ suffix ∧
      (suffix = [] ∨ suffix.head? = some (!bit)) := by
  induction tail with
  | nil => exact ⟨1, [], by omega, rfl, Or.inl rfl⟩
  | cons b rest ih =>
    by_cases hb : b = bit
    · subst b
      obtain ⟨rho, suffix, hrho, heq, hright⟩ := ih
      refine ⟨rho + 1, suffix, by omega, ?_, hright⟩
      simpa only [List.replicate_succ, List.cons_append]
        using congrArg (List.cons bit) heq
    · refine ⟨1, b :: rest, by omega, rfl, Or.inr ?_⟩
      simpa only [List.head?_cons, Option.some.injEq] using bool_eq_not_of_ne hb
end DeletionCode.MaximalRuns
