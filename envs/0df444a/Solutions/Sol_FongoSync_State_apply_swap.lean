-- Prove2me | solution 1 for FongoSync.State.apply_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:54.14185+00:00
-- url     : https://prove2.me/submissions/e9433c4c-90d2-469a-82fe-5a498cb93f70

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
import Theorems.Thm_FongoSync_apply_any_order


set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]
namespace FongoSync
namespace State
theorem _root_.solution (σ : String → String → Strategy) (st : State V) (a b : Change V)
    (h : Compatible a b) :
    State.apply σ (State.apply σ st a) b = State.apply σ (State.apply σ st b) a := by
  funext k
  simp only [State.apply]
  by_cases ha : k = a.key <;> by_cases hb : k = b.key
  · subst ha
    have hab : a.key = b.key := hb
    simp only [hb, ↓reduceIte]
    rw [← hab]
    apply apply_any_order
    intro hc
    have hv := h hab hc
    simp only [Change.entry] at hc ⊢
    rw [hv, hc]
  · subst ha
    have hab : a.key ≠ b.key := hb
    simp [hab]
  · subst hb
    have hab : b.key ≠ a.key := ha
    simp [hab]
  · simp [ha, hb]
end State
end FongoSync
