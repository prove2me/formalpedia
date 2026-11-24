-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.Walk.b_run_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:04.830806+00:00
-- url     : https://prove2.me/submissions/2f886ff8-b3ea-4571-bd34-39427a2518dc

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
namespace Walk
theorem _root_.solution {s : ℕ} {t : Vertex} {m : ℕ}
    (h : Walk (.p s) (List.replicate m b) t) : m ≤ s := by
  induction m generalizing s t with
  | zero => omega
  | succ m ih =>
    rw [List.replicate_succ] at h
    cases h with
    | cons he hw =>
      cases he with
      | pb j => have H := ih hw; omega
end Walk
end BalanceSpecification.OneSidedExample
