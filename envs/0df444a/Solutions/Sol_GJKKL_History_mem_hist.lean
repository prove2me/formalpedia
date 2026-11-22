-- Prove2me | solution 1 for GJKKL.History.mem_hist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:09.773254+00:00
-- url     : https://prove2.me/submissions/676ec6f3-9b37-49eb-be33-8639f40ec7d9

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace GJKKL.History
theorem _root_.solution {T : ℕ} {h : List α} : h ∈ hist α T ↔ h.length = T := by
  induction T generalizing h with
  | zero => cases h <;> simp [hist]
  | succ T ih =>
    cases h with
    | nil => simp [hist]
    | cons a h => simp [hist, ih]
end GJKKL.History
