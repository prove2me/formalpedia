-- Prove2me | solution 1 for CCS.op_to_den
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:13:13.421894+00:00
-- url     : https://prove2.me/submissions/c3e66ae5-b7c6-4918-912f-163669097ee9

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
import Theorems.Thm_CCS_Action_strip_map
import Theorems.Thm_CCS_Label_co_co
import Theorems.Thm_CCS_Label_strip_map
import Theorems.Thm_CCS_inlInv_insert
import Theorems.Thm_CCS_inrInv_insert
import Theorems.Thm_CCS_isConf_insert_tag
import Theorems.Thm_CCS_mem_unres
import Theorems.Thm_CCS_pfx_isConf
import Theorems.Thm_CCS_pfx_isConf_insert
import Theorems.Thm_CCS_pfx_none_mem
import Theorems.Thm_CCS_projL_insert
import Theorems.Thm_CCS_projL_insert_none
import Theorems.Thm_CCS_projL_isConf
import Theorems.Thm_CCS_projR_insert
import Theorems.Thm_CCS_projR_insert_none
import Theorems.Thm_CCS_projR_isConf
import Theorems.Thm_CCS_restrict_isConf
import Theorems.Thm_CCS_restrict_isConf_insert
import Theorems.Thm_CCS_someInv_insert
import Theorems.Thm_CCS_sum_isConf_L
import Theorems.Thm_CCS_sum_isConf_R
import Theorems.Thm_CCS_sum_isConf_insert_L
import Theorems.Thm_CCS_sum_isConf_insert_R
import Theorems.Thm_CCS_sum_not_mixed
import Theorems.Thm_CCS_unres_insert
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
    (α : Action Name) (Q' : Process Name), (semantics P).toGES.isConf c →
    Step (resid P c) α Q' →
    ∃ e, (semantics P).toGES.isConf (c ∪ {e}) ∧ e ∉ c ∧
      (semantics P).label e = α ∧ Q' = resid P (c ∪ {e})
  | _, .nil, c, α, Q', _, hstep => by
      rw [resid_nil] at hstep; cases hstep
  | _, .pre α₀ P, c, α, Q', hc, hstep => by
      by_cases hnone : none ∈ c
      · rw [resid_pre_pos hnone] at hstep
        obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ := solution P _ α Q' (pfx_isConf hc) hstep
        refine ⟨some x, ?_, fun h => hxfr h, hxlbl, ?_⟩
        · exact pfx_isConf_insert hc hnone (someInv_insert ▸ hxins) (fun h => hxfr h)
        · rw [resid_pre_pos (Or.inl hnone : none ∈ c ∪ {some x}), someInv_insert]
          exact hxQ
      · rw [resid_pre_neg hnone] at hstep
        cases hstep
        have hc0 : c = ∅ := by
          ext z
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hz
          cases z with
          | none => exact hnone hz
          | some w => exact hnone (pfx_none_mem hc hz)
        subst hc0
        refine ⟨none, ?_, by simp, rfl, ?_⟩
        · refine ⟨fun W hW V hV => ?_, ?_⟩
          · have : V = ∅ := by
              refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
              obtain ⟨u, hu, hev⟩ : ∃ u, u ∈ (W : Set (Option (semantics P).Event)) ∧ u = some z :=
                ⟨some z, hV (by exact_mod_cast hz), rfl⟩
              rcases hW hu with h | h
              · exact h.elim
              · exact absurd (hev ▸ Set.mem_singleton_iff.mp h) (by simp)
            exact this ▸ (semantics P).con_empty
          · rintro z (hz | hz)
            · exact hz.elim
            · replace hz : z = none := hz
              subst hz
              exact ⟨1, Or.inr rfl, ∅, by simp, trivial⟩
        · rw [resid_pre_pos (by simp : none ∈ (∅ : Set (semantics (.pre α₀ P)).Event) ∪ {none})]
          have h2 : {y : (semantics P).Event |
              some y ∈ (∅ : Set (semantics (.pre α₀ P)).Event) ∪ {none}} = ∅ := by
            ext y; simp
          rw [h2, resid_empty]
  | _, .sum P Q, c, α, Q', hc, hstep => by
      by_cases hexL : ∃ e, Sum.inl e ∈ c
      · have hnoR : ¬ ∃ f, Sum.inr f ∈ c := by
          rintro ⟨f, hf⟩
          obtain ⟨e, he⟩ := hexL
          exact sum_not_mixed hc he hf
        rw [resid_sum_l hexL] at hstep
        obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ := solution P _ α Q' (sum_isConf_L hc) hstep
        refine ⟨Sum.inl x, sum_isConf_insert_L hc hnoR (inlInv_insert ▸ hxins),
          fun h => hxfr h, hxlbl, ?_⟩
        rw [resid_sum_l ⟨x, Or.inr rfl⟩, inlInv_insert]
        exact hxQ
      by_cases hexR : ∃ f, Sum.inr f ∈ c
      · rw [resid_sum_r hexL hexR] at hstep
        obtain ⟨y, hyins, hyfr, hylbl, hyQ⟩ := solution Q _ α Q' (sum_isConf_R hc) hstep
        have hnoL' : ¬ ∃ e, Sum.inl e ∈ c ∪ ({Sum.inr y} : Set (semantics (.sum P Q)).Event) := by
          rintro ⟨e, he | he⟩
          · exact hexL ⟨e, he⟩
          · exact absurd (Set.mem_singleton_iff.mp he) (by simp)
        refine ⟨Sum.inr y, sum_isConf_insert_R hc hexL (inrInv_insert ▸ hyins),
          fun h => hyfr h, hylbl, ?_⟩
        rw [resid_sum_r hnoL' ⟨y, Or.inr rfl⟩, inrInv_insert]
        exact hyQ
      · have hc0 : c = ∅ := by
          ext z
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hz
          cases z with
          | inl w => exact hexL ⟨w, hz⟩
          | inr w => exact hexR ⟨w, hz⟩
        subst hc0
        rw [resid_sum_none hexL hexR] at hstep
        have hcE : (semantics (.sum P Q)).toGES.isConf ∅ := GES.isConf_empty _
        cases hstep with
        | sumL hs =>
          obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ :=
            solution P ∅ α _ (GES.isConf_empty _) (by rw [resid_empty]; exact hs)
          have hemp : {z : (semantics P).Event |
              Sum.inl z ∈ (∅ : Set (semantics (.sum P Q)).Event)} = ∅ := by ext z; simp
          refine ⟨Sum.inl x, sum_isConf_insert_L hcE hexR ?_, by simp, hxlbl, ?_⟩
          · rw [hemp]; exact hxins
          · rw [resid_sum_l ⟨x, Or.inr rfl⟩, inlInv_insert, hemp]; exact hxQ
        | sumR hs =>
          obtain ⟨y, hyins, hyfr, hylbl, hyQ⟩ :=
            solution Q ∅ α _ (GES.isConf_empty _) (by rw [resid_empty]; exact hs)
          have hemp : {z : (semantics Q).Event |
              Sum.inr z ∈ (∅ : Set (semantics (.sum P Q)).Event)} = ∅ := by ext z; simp
          have hnoL' : ¬ ∃ e, Sum.inl e ∈ (∅ : Set (semantics (.sum P Q)).Event) ∪ {Sum.inr y} := by
            rintro ⟨e, he | he⟩
            · exact he.elim
            · exact absurd (Set.mem_singleton_iff.mp he) (by simp)
          refine ⟨Sum.inr y, sum_isConf_insert_R hcE hexL ?_, by simp, hylbl, ?_⟩
          · rw [hemp]; exact hyins
          · rw [resid_sum_r hnoL' ⟨y, Or.inr rfl⟩, inrInv_insert, hemp]; exact hyQ
  | _, .res P, c, α, Q', hc, hstep => by
      rw [resid_res] at hstep
      cases hstep with
      | @res _ A _ A' hs =>
        obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ := solution P _ _ A' (restrict_isConf hc) hs
        have hx : ((semantics P).label x).strip.isSome = true := by rw [hxlbl]; simp
        refine ⟨⟨x, hx⟩, restrict_isConf_insert hc (unres_insert (c := c) hx ▸ hxins),
          fun hmem => hxfr ((mem_unres hx).mpr hmem), ?_, ?_⟩
        · change ((semantics P).label x).strip.get _ = α
          exact Option.some.inj
            ((Option.some_get _).trans (by rw [hxlbl]; exact Action.strip_map α))
        · rw [resid_res, unres_insert, hxQ]
          rfl
  | _, .par P Q, c, α, Q', hc, hstep => by
      rw [resid_par] at hstep
      cases hstep with
      | @parL _ _ _ A' _ hs =>
        obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ := solution P _ α A' (projL_isConf hc) hs
        refine ⟨Tag.left x, isConf_insert_tag hc ?_ ?_, ?_, hxlbl, ?_⟩
        · rintro x' hx'
          exact ⟨(Option.some.inj hx') ▸ hxins, (Option.some.inj hx') ▸ hxfr⟩
        · rintro y' hy'; exact absurd hy' (by simp [Tag.evR])
        · exact fun hmem => hxfr ⟨_, hmem, rfl⟩
        · rw [resid_par, projL_insert (rfl : (Tag.left x).evL = some x),
            projR_insert_none (rfl : (Tag.left x : Tag _ (semantics Q)).evR = none), ← hxQ]
      | @parR _ _ _ _ B' hs =>
        obtain ⟨y, hyins, hyfr, hylbl, hyQ⟩ := solution Q _ α B' (projR_isConf hc) hs
        refine ⟨Tag.right y, isConf_insert_tag hc ?_ ?_, ?_, hylbl, ?_⟩
        · rintro x' hx'; exact absurd hx' (by simp [Tag.evL])
        · rintro y' hy'
          exact ⟨(Option.some.inj hy') ▸ hyins, (Option.some.inj hy') ▸ hyfr⟩
        · exact fun hmem => hyfr ⟨_, hmem, rfl⟩
        · rw [resid_par,
            projL_insert_none (rfl : (Tag.right y : Tag (semantics P) _).evL = none),
            projR_insert (rfl : (Tag.right y).evR = some y), ← hyQ]
      | @parSync _ _ a _ _ _ hs1 hs2 =>
        obtain ⟨x, hxins, hxfr, hxlbl, hxQ⟩ := solution P _ _ _ (projL_isConf hc) hs1
        obtain ⟨y, hyins, hyfr, hylbl, hyQ⟩ := solution Q _ _ _ (projR_isConf hc) hs2
        refine ⟨Tag.sync x y ⟨a, hxlbl, hylbl⟩, isConf_insert_tag hc ?_ ?_, ?_, rfl, ?_⟩
        · rintro x' hx'
          exact ⟨(Option.some.inj hx') ▸ hxins, (Option.some.inj hx') ▸ hxfr⟩
        · rintro y' hy'
          exact ⟨(Option.some.inj hy') ▸ hyins, (Option.some.inj hy') ▸ hyfr⟩
        · exact fun hmem => hxfr ⟨_, hmem, rfl⟩
        · rw [resid_par, projL_insert (rfl : (Tag.sync x y _).evL = some x),
            projR_insert (rfl : (Tag.sync x y _).evR = some y), ← hxQ, ← hyQ]
end CCS
