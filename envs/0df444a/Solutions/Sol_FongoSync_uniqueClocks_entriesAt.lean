-- Prove2me | solution 1 for FongoSync.uniqueClocks_entriesAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:52.890633+00:00
-- url     : https://prove2.me/submissions/594e2b12-5f9d-49f2-9eb9-c10c3f9fdc7f

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
import Theorems.Thm_FongoSync_mem_entriesAt

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
namespace FongoSync
theorem _root_.solution {cs : List (Change V)} (h : ClockDetermines cs) (k : Key) :
    UniqueClocks (entriesAt cs k) := by
  intro a ha b hb hab
  obtain ⟨ca, hca, kca, rfl⟩ := mem_entriesAt.mp ha
  obtain ⟨cb, hcb, kcb, rfl⟩ := mem_entriesAt.mp hb
  have hv := h ca hca cb hcb (kca.trans kcb.symm) hab
  simp only [Change.entry] at hab ⊢
  rw [hv, hab]
end FongoSync
