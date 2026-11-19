-- Prove2me | solution 1 for DeletionCode.Recovery.State.frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:51:09.667363+00:00
-- url     : https://prove2.me/submissions/fbe9f9e8-ec68-4c58-98cb-0c9d600dd775

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open DeletionCode.Recovery.State
namespace DeletionCode.Recovery.State
theorem _root_.solution (s : State B) (b : B)
    (hb : s.Started b) (hi : ¬ s.Complete b) :
    ∃ w, s.Ready b w ∧ ¬ s.Done b w := by
  classical
  by_contra hn
  have hclosed : ∀ w, s.Ready b w → s.Done b w := by
    intro w hw
    by_contra hnot
    exact hn ⟨w, hw, hnot⟩
  cases hseed : s.seed b with
  | none => exact hb hseed
  | some v =>
    have hv : s.Done b v := hclosed v (Or.inl hseed)
    apply hi
    fin_cases v
    · have h1 : s.Done b 1 :=
        hclosed 1 (Or.inr ⟨0, hv, by norm_num [AdjSlot]⟩)
      have h2 : s.Done b 2 :=
        hclosed 2 (Or.inr ⟨1, h1, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
    · have h0 : s.Done b 0 :=
        hclosed 0 (Or.inr ⟨1, hv, by norm_num [AdjSlot]⟩)
      have h2 : s.Done b 2 :=
        hclosed 2 (Or.inr ⟨1, hv, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
    · have h1 : s.Done b 1 :=
        hclosed 1 (Or.inr ⟨2, hv, by norm_num [AdjSlot]⟩)
      have h0 : s.Done b 0 :=
        hclosed 0 (Or.inr ⟨1, h1, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
end DeletionCode.Recovery.State
