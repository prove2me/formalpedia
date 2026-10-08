-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.single_mem_mulDomain
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T04:46:05.9377+00:00
-- url     : https://prove2.me/submissions/9b6274d4-3155-4fc7-9153-58d7e026ceeb

import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite

open BookProof.ChapterContinuityUnitaryInfinite BookProof.ChapterUnboundedPosition in
theorem solution (f : ℤ → ℝ) (n : ℤ) (c : ℂ) :
    lp.single 2 n c ∈ mulDomain f := by
  change Memℓp (fun k => (f k : ℂ) * ((lp.single 2 n c : L2Z) : ℤ → ℂ) k) 2
  have heq : (fun k => (f k : ℂ) * ((lp.single 2 n c : L2Z) : ℤ → ℂ) k)
      = ((lp.single 2 n ((f n : ℂ) * c) : L2Z) : ℤ → ℂ) := by
    funext k
    by_cases h : k = n
    · subst h; simp
    · simp [h]
  rw [heq]
  exact (lp.single 2 n ((f n : ℂ) * c) : L2Z).2
