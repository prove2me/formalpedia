-- Prove2me | solution 1 for GL2QFT.theorem_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:11:26.453833+00:00
-- url     : https://prove2.me/submissions/f6c142fc-4e68-4fe6-a852-368c4c9f4346
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GL2QFT_Uniform
import Theorems.Thm_GL2QFT_theorem_6_13
import Theorems.Thm_GL2QFT_Supplement_theorem_6_14
import Theorems.Thm_GL2QFT_Circuits_qftGL2_of_mackey_bridge

open Classical

theorem solution :
    GL2QFT.UniformlyImplementsOn (fun _ => True)
      (X := fun D => D.G) (Y := fun D => D.OutLabel)
      (inW := fun D => 4 * D.r * D.digitW) (outW := fun D => 5 * D.labW)
      (fun D => D.inCode) (fun D => D.outCode) (fun D => D.qftGL2) :=
  GL2QFT.Circuits.qftGL2_of_mackey_bridge GL2QFT.theorem_6_13 GL2QFT.Supplement.theorem_6_14
