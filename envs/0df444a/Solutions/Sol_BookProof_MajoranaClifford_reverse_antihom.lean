-- Prove2me | solution 1 for BookProof.MajoranaClifford.reverse_antihom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:19:25.751015+00:00
-- url     : https://prove2.me/submissions/9988003c-cf23-4ec2-a61a-b648dd623c97

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.reverse_antihom
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution (x y : CliffordAlgebra (Qform (V := V))) :
    reverse (x * y) = reverse y * reverse x := reverse.map_mul x y
