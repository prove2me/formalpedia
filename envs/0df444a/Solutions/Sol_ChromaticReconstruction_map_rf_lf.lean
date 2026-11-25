-- Prove2me | solution 1 for ChromaticReconstruction.map_rf_lf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:14:56.612902+00:00
-- url     : https://prove2.me/submissions/294ba2c6-693a-4621-8969-fdeea5f07412

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_map_rf_vx

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))}
namespace ChromaticReconstruction
theorem _root_.solution {s : ℕ} (hn : 2 * c + 3 ≤ n) (hp : p = c ∨ p = c + 1) (hs1 : 1 ≤ s)
    (hs2 : s ≤ c + 1) : Sym2.map (rf n c s) (lf n p) = lf n (2 * c + 1 - p) := by
  rw [lf, map_rf_vx (by omega) le_rfl]
  have e1 : rfv c s p = 2 * c + 1 - p := by unfold rfv; split_ifs <;> omega
  have e2 : rfv c s n = n := by unfold rfv; split_ifs <;> omega
  rw [e1, e2, lf]
end ChromaticReconstruction
