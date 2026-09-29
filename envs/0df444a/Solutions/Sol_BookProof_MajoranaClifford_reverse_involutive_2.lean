-- Prove2me | solution 2 for BookProof.MajoranaClifford.reverse_involutive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:22:25.2766+00:00
-- url     : https://prove2.me/submissions/efc9a150-8ba4-4f79-9673-7f1d33840405

-- Generated from ChapterMajoranaClifford.lean — solution of BookProof.MajoranaClifford.reverse_involutive
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford










open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

set_option maxHeartbeats 1000000 in
theorem solution :
    Function.Involutive (reverse : CliffordAlgebra (Qform (V := V)) → _) := fun x => reverse_reverse x
