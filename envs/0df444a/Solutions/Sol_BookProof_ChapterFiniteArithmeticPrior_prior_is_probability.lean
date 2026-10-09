-- Prove2me | solution 1 for BookProof.ChapterFiniteArithmeticPrior.prior_is_probability
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:11:24.659478+00:00
-- url     : https://prove2.me/submissions/75c043ec-76c9-437c-af6b-eb10acf74161

-- Generated from ChapterFiniteArithmeticPrior.lean — solution of BookProof.ChapterFiniteArithmeticPrior.prior_is_probability
import Mathlib
import Definitions.Def_ChapterFiniteArithmeticPrior
open BookProof.ChapterFiniteArithmeticPrior

set_option maxHeartbeats 1000000 in
theorem solution {B : ℕ} {H : Type*} [Fintype H]
    (E : BayesianArithmeticExtension B H) :
    (∀ h, 0 ≤ E.prior h) ∧ ∑ h, E.prior h = 1 := by

  exact ⟨E.prior_nonneg, E.prior_sum_one⟩
