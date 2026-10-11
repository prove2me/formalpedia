-- Prove2me | solution 1 for BookProof.SmBrstGhost.sumStruct_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:54:01.255294+00:00
-- url     : https://prove2.me/submissions/a5895604-ed65-4315-83a3-cc4cb53dd333

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.sumStruct_antisymm
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {ι κ : Type*} {f1 : ι → ι → ι → ℝ}
    {f2 : κ → κ → κ → ℝ} (h1 : ∀ a b c, f1 a b c = -f1 b a c)
    (h2 : ∀ a b c, f2 a b c = -f2 b a c) (a b c : ι ⊕ κ) :
    sumStruct f1 f2 a b c = -sumStruct f1 f2 b a c := by

  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
    simp only [sumStruct, neg_zero] <;> first | rfl | exact h1 a b c | exact h2 a b c
