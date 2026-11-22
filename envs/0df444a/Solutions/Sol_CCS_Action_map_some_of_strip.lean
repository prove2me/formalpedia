-- Prove2me | solution 1 for CCS.Action.map_some_of_strip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:08:42.1488+00:00
-- url     : https://prove2.me/submissions/8fea70b3-9864-4a91-9fa1-0e47caccb23b

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Definitions.Def_EventStructures_CCS_Syntax
import Theorems.Thm_CCS_Label_co_co
import Theorems.Thm_CCS_Label_strip_map
import Theorems.Thm_CCS_Action_strip_map
attribute [local simp] CCS.Label.co_co
attribute [local simp] CCS.Label.strip_map
attribute [local simp] CCS.Action.strip_map

set_option autoImplicit true
open CCS
open CCS.Action
variable {Name Name' : Type*}
namespace CCS.Action
theorem _root_.solution : ∀ {b : Action (Option Name)} {a : Action Name},
    b.strip = some a → b = Action.map some a
  | vis l, a, h => by
      cases l with
      | inp n => cases n with
        | none => simp [Action.strip, Label.strip] at h
        | some m => cases a with
          | vis l' => simp [Action.strip, Label.strip] at h; simp [Action.map, Label.map, ← h]
          | tau => simp [Action.strip, Label.strip] at h
      | out n => cases n with
        | none => simp [Action.strip, Label.strip] at h
        | some m => cases a with
          | vis l' => simp [Action.strip, Label.strip] at h; simp [Action.map, Label.map, ← h]
          | tau => simp [Action.strip, Label.strip] at h
  | tau, a, h => by simp [Action.strip] at h; simp [← h, Action.map]
end CCS.Action
