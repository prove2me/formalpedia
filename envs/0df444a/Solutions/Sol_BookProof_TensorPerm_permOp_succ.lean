-- Prove2me | solution 1 for BookProof.TensorPerm.permOp_succ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:16.835547+00:00
-- url     : https://prove2.me/submissions/e6372c76-e357-477c-adb2-e6953a7ba60e

-- Generated from ChapterTensorPermutation.lean — solution of BookProof.TensorPerm.permOp_succ
import Mathlib
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorPerm




open scoped TensorProduct
open BookProof.TensorCore BookProof.GroupAverage

noncomputable section

variable (E : BookProof.TensorCore.IPSpace)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    permOp E (n + 1) σ = (swap0 E (n + 1) (Equiv.Perm.decomposeFin σ).1).trans
      (liftTail E (permOp E n (Equiv.Perm.decomposeFin σ).2)) := rfl
