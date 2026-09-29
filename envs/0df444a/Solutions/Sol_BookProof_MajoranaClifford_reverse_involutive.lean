-- Prove2me | solution 1 for BookProof.MajoranaClifford.reverse_involutive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:21:05.069538+00:00
-- url     : https://prove2.me/submissions/66ed55af-07d1-465d-8409-692d7df732c3

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.reverse_involutive
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution :
    Function.Involutive (reverse : CliffordAlgebra (Qform (V := V)) → _) := fun x => reverse_reverse x
