-- Prove2me | solution 1 for CCS.pfx_isConf_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:10:48.24072+00:00
-- url     : https://prove2.me/submissions/70d9749e-925c-463c-8014-85a543693390

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Prime_LTSI
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Definitions.Def_EventStructures_CCS_Semantics
import Theorems.Thm_CCS_pmapSet_pfx
import Theorems.Thm_GES_isConf_insert_pmap


set_option autoImplicit true
open PES Configuration ConfFamily
open CCS
variable {Name : Type*}
variable {Name : Type*}
variable {E F : SES (Action Name)} {α : Action Name}
namespace CCS
theorem _root_.solution {c : Set (Option E.Event)} {x : E.Event}
    (hc : (pfx α E).toGES.isConf c) (hnone : none ∈ c)
    (hx : E.toGES.isConf ({z | some z ∈ c} ∪ {x})) (_hfr : some x ∉ c) :
    (pfx α E).toGES.isConf (c ∪ {some x}) := by
  classical
  refine GES.isConf_insert_pmap (G := (pfx α E).toGES) (H := E.toGES) id hc rfl ?_ ?_
    ((pmapSet_pfx (α := α) c) ▸ hx)
  · intro W hW V hV
    refine hx.1 V fun z hz => ?_
    obtain ⟨u, hu, hev⟩ : ∃ u, u ∈ (W : Set (Option E.Event)) ∧ u = some z := ⟨some z, hV hz, rfl⟩
    subst hev
    rcases hW hu with h | h
    · exact Or.inl h
    · exact Or.inr (Option.some.inj (Set.mem_singleton_iff.mp h))
  · intro Y hY hen
    refine ⟨insert none (Y.image some), ?_, ⟨Finset.mem_insert_self _ _, Y, ?_, hen⟩⟩
    · intro u hu
      rcases Finset.mem_insert.mp (by exact_mod_cast hu) with rfl | hu'
      · exact hnone
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu'
        obtain ⟨v, hv, hev⟩ := hY y hy
        exact hev ▸ hv
    · intro y hy
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
end CCS
