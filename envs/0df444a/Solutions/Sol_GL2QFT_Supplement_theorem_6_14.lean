-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_6_14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:14:32.464031+00:00
-- url     : https://prove2.me/submissions/b5be9bd1-36f3-484f-9d0d-186d816963dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GL2QFT_Supplement_TotalA
import Theorems.Thm_GL2QFT_theorem_6_34
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_by_q2
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_mono
import Theorems.Thm_GL2QFT_Circuits_totalA_routing_and_small_blocks

open Classical

theorem solution :
    GL2QFT.UniformlyImplementsOn (fun _ => True)
      (X := fun D => GL2QFT.Supplement.TotalA.InReg D)
      (Y := fun D => GL2QFT.Supplement.TotalA.OutReg D)
      (inW := fun D => 10 * D.labW) (outW := fun D => 9 * D.labW)
      (fun D => GL2QFT.Supplement.TotalA.inCodeA D)
      (fun D => GL2QFT.Supplement.TotalA.outCodeA D)
      (fun D => GL2QFT.Supplement.TotalA.totalA D) :=
  GL2QFT.Circuits.uniformlyImplementsOn_by_q2
    (GL2QFT.Circuits.uniformlyImplementsOn_mono
      GL2QFT.Circuits.totalA_routing_and_small_blocks.1 (fun _ h => h.2))
    (GL2QFT.Circuits.uniformlyImplementsOn_mono
      (GL2QFT.Circuits.totalA_routing_and_small_blocks.2 GL2QFT.theorem_6_34)
      (fun _ h => h.2))
