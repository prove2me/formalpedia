-- Prove2me | solution 1 for BalanceSpecification.zeros_marker_prefix_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:14.906323+00:00
-- url     : https://prove2.me/submissions/e93c4d0d-1d90-4618-8390-54071ea1fb7d

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {s t : ℕ} (hst : s < t) {u v : Word Bool}
    (hu : u = [] ∨ ∃ z, u = true :: z) :
    List.replicate s false ++ u ≠ List.replicate t false ++ v := by
  intro heq
  have ht : t = s + (t - s) := by omega
  rw [ht, List.replicate_add, List.append_assoc] at heq
  have htail := (List.append_right_inj _).mp heq
  have hdiff : t - s ≠ 0 := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hdiff
  rw [hk, List.replicate_succ, List.cons_append] at htail
  obtain rfl | ⟨z, rfl⟩ := hu
  · cases htail
  · cases List.head_eq_of_cons_eq htail
end BalanceSpecification
