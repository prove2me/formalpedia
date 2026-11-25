-- Prove2me | solution 1 for ChromaticReconstruction.map_rf_vx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:03:54.5959+00:00
-- url     : https://prove2.me/submissions/365b07e8-2a7c-4bb5-b096-56cf8d29cb01

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_rf_vx

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution {s a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    Sym2.map (rf n c s) s(vx n a, vx n b) = s(vx n (rfv c s a), vx n (rfv c s b)) := by
  rw [Sym2.map_pair_eq, rf_vx ha, rf_vx hb]
end ChromaticReconstruction
