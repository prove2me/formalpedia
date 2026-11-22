-- Prove2me | solution 1 for CCS.restrict_isConf_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:10:52.566308+00:00
-- url     : https://prove2.me/submissions/94d2bcc5-867c-4ffa-a118-75a18b405a38

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
import Theorems.Thm_CCS_pmapSet_unres
import Theorems.Thm_Bisimilar_symm
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_GES_isConf_insert_pmap


set_option autoImplicit true
open PES Configuration ConfFamily
open CCS
variable {Name : Type*}
variable {Name : Type*}
variable {E F : SES (Action Name)} {α : Action Name}
namespace CCS
theorem _root_.solution {E : SES (Action (Option Name))} {c : Set (restrict E).Event}
    {x : E.Event} {hx : (E.label x).strip.isSome = true}
    (hc : (restrict E).toGES.isConf c)
    (hxc : E.toGES.isConf ({y | ∃ hy, (⟨y, hy⟩ : (restrict E).Event) ∈ c} ∪ {x})) :
    (restrict E).toGES.isConf (c ∪ {⟨x, hx⟩}) := by
  classical
  refine GES.isConf_insert_pmap (G := (restrict E).toGES) (H := E.toGES)
    (fun e => some e.1) hc rfl ?_ ?_ ((pmapSet_unres c) ▸ hxc)
  · intro W hW V hV
    refine hxc.1 V fun z hz => ?_
    obtain ⟨hv, hm⟩ := hV hz
    rcases hW hm with h | h
    · exact Or.inl ⟨hv, h⟩
    · exact Or.inr (congrArg Subtype.val (Set.mem_singleton_iff.mp h))
  · intro Y hY hen
    refine ⟨Y.attach.image fun y => (hY y.1 y.2).choose, ?_, Y, ?_, hen⟩
    · intro u hu
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hu)
      exact (hY y.1 y.2).choose_spec.1
    · intro y hy
      have hval : ((hY y hy).choose).1 = y :=
        Option.some.inj (hY y hy).choose_spec.2
      refine ⟨hval ▸ ((hY y hy).choose).2, ?_⟩
      have hmem : (hY y hy).choose ∈
          Y.attach.image (fun z => (hY z.1 z.2).choose) :=
        Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩
      have : (⟨y, hval ▸ ((hY y hy).choose).2⟩ : (restrict E).Event) = (hY y hy).choose :=
        Subtype.ext hval.symm
      rw [this]
      exact_mod_cast hmem
end CCS
