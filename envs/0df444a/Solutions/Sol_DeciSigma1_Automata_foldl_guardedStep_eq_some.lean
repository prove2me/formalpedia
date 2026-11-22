-- Prove2me | solution 1 for DeciSigma1.Automata.foldl_guardedStep_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:33:45.324406+00:00
-- url     : https://prove2.me/submissions/51c5a2b0-e34c-4d86-966c-47d5090f54ae

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Theorems.Thm_DeciSigma1_Automata_foldl_guardedStep

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
open DeciSigma1.Constraints
open DeciSigma1.Automata
variable {α S T : Type}
variable (f : S → α → S) (g : T → α → T) (good : S → T → Prop) [∀ s t, Decidable (good s t)]
namespace DeciSigma1.Automata
theorem _root_.solution (s : S) (t : T) {w : List α}
    (h : w.foldl (guardedStep f g good) (guardedPair good s t) ≠ none) :
    w.foldl (guardedStep f g good) (guardedPair good s t) = some (w.foldl f s, w.foldl g t) := by
  rw [foldl_guardedStep] at h ⊢
  split_ifs at h ⊢
  · rfl
  · exact absurd rfl h
end DeciSigma1.Automata
