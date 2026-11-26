-- Prove2me | solution 1 for C6BipartiteDomination.paperChosenRepairSet_legal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:54:17.17524+00:00
-- url     : https://prove2.me/submissions/65e02420-a8d7-4910-9765-86bf0fee9f80

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    ∀ u ∈ paperChosenRepairSet G D hCan hmax w,
      IsRepairVertex G D w u := by
  classical
  have hcond : w ∈ SPart G D ∧ externalCharge G D w < 0 := ⟨hw, ha⟩
  simp only [paperChosenRepairSet, dif_pos hcond]
  exact (Classical.choose_spec
    (paper8_chosen_repair_witness G hCan hmax hw ha)).1
end C6BipartiteDomination
