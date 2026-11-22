-- Prove2me | solution 1 for CCS.den_to_op
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:13:08.283652+00:00
-- url     : https://prove2.me/submissions/88a23b82-269e-4e15-ac70-8de3314bdee1

import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_CCS_Semantics
import Definitions.Def_EventStructures_CCS_Bisimulation
import Theorems.Thm_CCS_resid_nil
import Theorems.Thm_CCS_resid_pre_pos
import Theorems.Thm_CCS_resid_pre_neg
import Theorems.Thm_CCS_resid_sum_l
import Theorems.Thm_CCS_resid_sum_r
import Theorems.Thm_CCS_resid_sum_none
import Theorems.Thm_CCS_resid_par
import Theorems.Thm_CCS_resid_res
import Theorems.Thm_CCS_resid_empty
import Theorems.Thm_Bisimilar_symm
import Theorems.Thm_CCS_Action_map_some_of_strip
import Theorems.Thm_CCS_Action_strip_map
import Theorems.Thm_CCS_Label_co_co
import Theorems.Thm_CCS_Label_strip_map
import Theorems.Thm_CCS_enables_projL
import Theorems.Thm_CCS_enables_projR
import Theorems.Thm_CCS_inlInv_insert
import Theorems.Thm_CCS_inrInv_insert
import Theorems.Thm_CCS_mem_unres
import Theorems.Thm_CCS_pfx_isConf
import Theorems.Thm_CCS_pfx_none_mem
import Theorems.Thm_CCS_projL_insert
import Theorems.Thm_CCS_projL_insert_none
import Theorems.Thm_CCS_projL_isConf
import Theorems.Thm_CCS_projR_insert
import Theorems.Thm_CCS_projR_insert_none
import Theorems.Thm_CCS_projR_isConf
import Theorems.Thm_CCS_restrict_isConf
import Theorems.Thm_CCS_someInv_insert
import Theorems.Thm_CCS_sum_isConf_L
import Theorems.Thm_CCS_sum_isConf_R
import Theorems.Thm_CCS_sum_not_mixed
import Theorems.Thm_CCS_unres_insert
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_GES_toFamily_Config
import Theorems.Thm_GES_toFamily_Event
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_toFamily_Config
import Theorems.Thm_PES_toFamily_Event
import Theorems.Thm_SES_toFamily_Config
attribute [local simp] CCS.Action.strip_map
attribute [local simp] CCS.Label.co_co
attribute [local simp] CCS.Label.strip_map
attribute [local simp] GES.toFamily_Config
attribute [local simp] GES.toFamily_Event
attribute [local simp] PES.enables_iff
attribute [local simp] PES.toFamily_Config
attribute [local simp] PES.toFamily_Event
attribute [local simp] SES.toFamily_Config


attribute [local simp] CCS.resid_nil
attribute [local simp] CCS.resid_empty

set_option autoImplicit true
open CCS ConfFamily
open CCS
universe u
variable {Name : Type u}
namespace CCS
theorem _root_.solution : ∀ {Name : Type u} (P : Process Name) (c : Set (semantics P).Event)
    (e : (semantics P).Event), (semantics P).toGES.isConf c →
    (semantics P).toGES.isConf (c ∪ {e}) → e ∉ c →
    Step (resid P c) ((semantics P).label e) (resid P (c ∪ {e}))
  | _, .nil, _, e, _, _, _ => e.elim
  | _, .pre α P, c, e, hc, hins, hfr => by
    cases e with
    | none =>
        have hc0 : c = ∅ := by
          ext z
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hz
          cases z with
          | none => exact hfr hz
          | some w => exact hfr (pfx_none_mem hc hz)
        subst hc0
        rw [resid_pre_neg (by simp)]
        have h1 : (∅ ∪ {none} : Set (semantics (.pre α P)).Event) = {none} := by simp
        rw [h1, resid_pre_pos (by simp)]
        have h2 : {y : (semantics P).Event |
            some y ∈ ({none} : Set (semantics (.pre α P)).Event)} = ∅ := by ext y; simp
        rw [h2, resid_empty]
        exact Step.pre
    | some x =>
        have hnone : none ∈ c := by
          rcases pfx_none_mem hins (Or.inr rfl : some x ∈ c ∪ {some x}) with h | h
          · exact h
          · exact absurd (Set.mem_singleton_iff.mp h) (by simp)
        rw [resid_pre_pos hnone, resid_pre_pos (Or.inl hnone : none ∈ c ∪ {some x}),
          someInv_insert]
        exact solution P _ x (pfx_isConf hc) (someInv_insert ▸ pfx_isConf hins)
          (fun h => hfr h)
  | _, .sum P Q, c, e, hc, hins, hfr => by
    cases e with
    | inl x =>
        have hnoR : ¬ ∃ f, Sum.inr f ∈ c := by
          rintro ⟨f, hf⟩
          exact sum_not_mixed hins (Or.inr rfl : Sum.inl x ∈ c ∪ {Sum.inl x}) (Or.inl hf)
        have hexNew : ∃ y, Sum.inl y ∈ c ∪ ({Sum.inl x} : Set (semantics (.sum P Q)).Event) :=
          ⟨x, Or.inr rfl⟩
        have ih := solution P _ x (sum_isConf_L hc) (inlInv_insert ▸ sum_isConf_L hins)
          (fun h => hfr h)
        by_cases hex : ∃ y, Sum.inl y ∈ c
        · rw [resid_sum_l hex, resid_sum_l hexNew, inlInv_insert]
          exact ih
        · have hc0 : {y : (semantics P).Event | Sum.inl y ∈ c} = ∅ := by
            ext y
            simp only [Set.mem_empty_iff_false, iff_false]
            exact fun h => hex ⟨y, h⟩
          rw [resid_sum_none hex hnoR, resid_sum_l hexNew, inlInv_insert, hc0]
          rw [hc0, resid_empty] at ih
          exact Step.sumL ih
    | inr y =>
        have hnoL : ¬ ∃ e, Sum.inl e ∈ c := by
          rintro ⟨e, he⟩
          exact sum_not_mixed hins (Or.inl he) (Or.inr rfl : Sum.inr y ∈ c ∪ {Sum.inr y})
        have hnoL' : ¬ ∃ e, Sum.inl e ∈ c ∪ ({Sum.inr y} : Set (semantics (.sum P Q)).Event) := by
          rintro ⟨e, he | he⟩
          · exact hnoL ⟨e, he⟩
          · exact absurd (Set.mem_singleton_iff.mp he) (by simp)
        have hexNew : ∃ z, Sum.inr z ∈ c ∪ ({Sum.inr y} : Set (semantics (.sum P Q)).Event) :=
          ⟨y, Or.inr rfl⟩
        have ih := solution Q _ y (sum_isConf_R hc) (inrInv_insert ▸ sum_isConf_R hins)
          (fun h => hfr h)
        by_cases hex : ∃ z, Sum.inr z ∈ c
        · rw [resid_sum_r hnoL hex, resid_sum_r hnoL' hexNew, inrInv_insert]
          exact ih
        · have hc0 : {z : (semantics Q).Event | Sum.inr z ∈ c} = ∅ := by
            ext z
            simp only [Set.mem_empty_iff_false, iff_false]
            exact fun h => hex ⟨z, h⟩
          rw [resid_sum_none hnoL hex, resid_sum_r hnoL' hexNew, inrInv_insert, hc0]
          rw [hc0, resid_empty] at ih
          exact Step.sumR ih
  | _, .res P, c, e, hc, hins, hfr => by
      obtain ⟨x, hx⟩ := e
      rw [resid_res, resid_res, unres_insert]
      refine Step.res ?_
      have ih := solution P _ x (restrict_isConf hc)
        (unres_insert (c := c) hx ▸ restrict_isConf hins)
        (fun h => hfr ((mem_unres hx).mp h))
      rwa [show (semantics P).label x
            = Action.map some ((semantics (.res P)).label ⟨x, hx⟩) from
          Action.map_some_of_strip (Option.some_get _).symm] at ih
  | _, .par P Q, c, t, hc, hins, hfr => by
      rcases t with x | y | ⟨x, y, hpf⟩
      · obtain ⟨hxen, hxfr⟩ := enables_projL hins hfr (rfl : (Tag.left x).evL = some x)
        rw [resid_par, resid_par, projL_insert (rfl : (Tag.left x).evL = some x),
          projR_insert_none (rfl : (Tag.left x : Tag _ (semantics Q)).evR = none)]
        exact Step.parL (solution P _ x (projL_isConf hc) hxen hxfr)
      · obtain ⟨hyen, hyfr⟩ := enables_projR hins hfr (rfl : (Tag.right y).evR = some y)
        rw [resid_par, resid_par,
          projL_insert_none (rfl : (Tag.right y : Tag (semantics P) _).evL = none),
          projR_insert (rfl : (Tag.right y).evR = some y)]
        exact Step.parR (solution Q _ y (projR_isConf hc) hyen hyfr)
      · obtain ⟨hxen, hxfr⟩ := enables_projL hins hfr (rfl : (Tag.sync x y hpf).evL = some x)
        obtain ⟨hyen, hyfr⟩ := enables_projR hins hfr (rfl : (Tag.sync x y hpf).evR = some y)
        obtain ⟨a, hax, hay⟩ := hpf
        rw [resid_par, resid_par, projL_insert (rfl : (Tag.sync x y _).evL = some x),
          projR_insert (rfl : (Tag.sync x y _).evR = some y)]
        exact Step.parSync (a := a)
          (hax ▸ solution P _ x (projL_isConf hc) hxen hxfr)
          (hay ▸ solution Q _ y (projR_isConf hc) hyen hyfr)
end CCS
