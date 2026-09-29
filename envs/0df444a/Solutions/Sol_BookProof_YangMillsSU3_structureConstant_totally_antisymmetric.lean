-- Prove2me | solution 1 for BookProof.YangMillsSU3.structureConstant_totally_antisymmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:28:44.9485+00:00
-- url     : https://prove2.me/submissions/200845c3-2679-45b4-80ce-8c5a27c4415e

-- Generated from ChapterYangMillsSU3.lean — solution of BookProof.YangMillsSU3.structureConstant_totally_antisymmetric
import Mathlib
import Definitions.Def_ChapterYangMillsSU3
import Theorems.Thm_BookProof_YangMillsSU3_structureConstant_antisymm_swap
import Theorems.Thm_BookProof_YangMillsSU3_structureConstant_antisymm_rotate
open BookProof.YangMillsSU3








open Matrix BigOperators


variable {n d : ℕ}
variable (T : Fin d → Matrix (Fin n) (Fin n) ℂ)
variable (f : Fin d → Fin d → Fin d → ℝ)



variable {T f}

set_option maxHeartbeats 1000000 in
theorem solution
    (hT : TraceOrthonormal T) (hf : ClosesWithStructureConstants T f) :
    (∀ a b c, f a b c = - f b a c) ∧ (∀ a b c, f a b c = - f a c b) := ⟨structureConstant_antisymm_swap hT hf, structureConstant_antisymm_rotate hT hf⟩
