-- Prove2me | solution 1 for BookProof.FockWeightedSchur.norm_oscCol_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:59:50.120561+00:00
-- url     : https://prove2.me/submissions/56d84338-cb6c-4419-b15b-08e6127f14a7

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.norm_oscCol_apply
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_oscCol_apply
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (k j : ℕ) : ‖(oscCol k) j‖ =
    if j = k + 1 then Real.sqrt ((k : ℝ) + 1)
    else if k = j + 1 then Real.sqrt (k : ℝ) else 0 := by

  rw [oscCol_apply]
  by_cases h1 : j = k + 1
  · rw [if_pos h1, if_pos h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  · by_cases h2 : k = j + 1
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, norm_zero]
