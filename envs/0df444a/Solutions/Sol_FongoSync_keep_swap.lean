-- Prove2me | solution 1 for FongoSync.keep_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:58:13.110865+00:00
-- url     : https://prove2.me/submissions/9c0447e9-0080-4d6d-8142-96fb5887728c

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}
namespace FongoSync
theorem _root_.solution (h : Option E) (a b : E) (inj : key a = key b → a = b) :
    keep cmp key (keep cmp key h a) b = keep cmp key (keep cmp key h b) a := by
  have tri : cmp (key a) (key b) = .lt ∨ a = b ∨ cmp (key b) (key a) = .lt := by
    cases hab : cmp (key a) (key b) with
    | lt => exact .inl rfl
    | eq => exact .inr (.inl (inj (LawfulEqCmp.eq_of_compare hab)))
    | gt => exact .inr (.inr (OrientedCmp.lt_of_gt hab))
  rcases tri with hab | rfl | hba
  · have hba : cmp (key b) (key a) ≠ .lt := fun h' => by
      have := OrientedCmp.gt_of_lt hab; simp_all
    cases h with
    | none => simp [hab, hba]
    | some s =>
      by_cases hsa : cmp (key s) (key a) = .lt
      · have hsb : cmp (key s) (key b) = .lt := TransCmp.lt_trans hsa hab
        simp [*]
      · by_cases hsb : cmp (key s) (key b) = .lt
        · simp [*]
        · simp [hsa, hsb]
  · rfl
  · have hab : cmp (key a) (key b) ≠ .lt := fun h' => by
      have := OrientedCmp.gt_of_lt hba; simp_all
    cases h with
    | none => simp [hab, hba]
    | some s =>
      by_cases hsb : cmp (key s) (key b) = .lt
      · have hsa : cmp (key s) (key a) = .lt := TransCmp.lt_trans hsb hba
        simp [*]
      · by_cases hsa : cmp (key s) (key a) = .lt
        · simp [*]
        · simp [hsa, hsb]
end FongoSync
