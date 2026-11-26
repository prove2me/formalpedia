-- Prove2me | solution 1 for C6BipartiteDomination.paper11_chosen_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:55:34.317689+00:00
-- url     : https://prove2.me/submissions/73cc5bfc-98b0-494e-84a0-a1627736233c

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ SPart G D) (ha : externalCharge G D w < 0) :
    ((kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧
        (paperChosenRepairSet G D hCan hmax w).card = 2) ∨
      (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧
        (paperChosenRepairSet G D hCan hmax w).card = 1) ∨
      (kCharge G D w = 4 ∧ betaCharge G D w = 2 ∧
        (paperChosenRepairSet G D hCan hmax w).card = 2)) := by
  classical
  have hcond : w ∈ SPart G D ∧ externalCharge G D w < 0 := ⟨hw, ha⟩
  simp only [paperChosenRepairSet, dif_pos hcond]
  exact (Classical.choose_spec
    (paper8_chosen_repair_witness G hCan hmax hw ha)).2
end C6BipartiteDomination
