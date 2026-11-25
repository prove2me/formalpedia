-- Prove2me | solution 1 for ChromaticReconstruction.mem_image_rf_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:16:31.268229+00:00
-- url     : https://prove2.me/submissions/54282471-8f3f-48b1-afe2-1cbcaa85507c

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_rf_involutive
import Theorems.Thm_ChromaticReconstruction_map_rf_vx
import Theorems.Thm_ChromaticReconstruction_mem_image_involutive

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))}
namespace ChromaticReconstruction
theorem _root_.solution {s a b : ℕ} (hs : c + s ≤ n) (hs' : s ≤ c + 1) (ha : a ≤ n) (hb : b ≤ n) :
    s(vx n a, vx n b) ∈ F.image (Sym2.map (rf n c s)) ↔
      s(vx n (rfv c s a), vx n (rfv c s b)) ∈ F := by
  rw [mem_image_involutive (rf_involutive hs hs'), map_rf_vx ha hb]
end ChromaticReconstruction
