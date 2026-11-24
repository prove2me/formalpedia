-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.Walk.start_of_probe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:49.516024+00:00
-- url     : https://prove2.me/submissions/76f07787-7865-4aee-be2f-d77f6c919275

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_b_run_length_le

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
namespace Walk
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {s t : Vertex}
    (h : Walk s (a :: List.replicate (n + 1) b) t) :
    ∃ k : ℕ, s = .q k ∧ n ≤ k + 1 := by
  cases h with
  | cons he hw =>
    cases he with
    | qa k =>
      rw [List.replicate_succ] at hw
      cases hw with
      | cons he hw =>
        cases he with
        | qb i => exact ⟨k, rfl, hw.b_run_length_le⟩
    | pa =>
      rw [List.replicate_succ] at hw
      cases hw with
      | cons he hw =>
        cases he with
        | qb i => have H := hw.b_run_length_le; omega
end Walk
end BalanceSpecification.OneSidedExample
