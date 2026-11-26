-- Prove2me | solution 1 for FD1D.hazard_energy_telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:44.076418+00:00
-- url     : https://prove2.me/submissions/7f3b2882-0a42-469e-96fb-5ea7ccb860d9

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_weighted_tree_telescope
import Theorems.Thm_FD1D_hazardEnergy_root

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (h : ∀ d, DyadicNode d → ℝ) (L : ℕ) :
    ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2) =
      hazardEnergy h L - hazardEnergy h 0 := by
  rw [hazardEnergy_root]
  exact weighted_tree_telescope (fun d v => (h d v) ^ 2) L
end FD1D
