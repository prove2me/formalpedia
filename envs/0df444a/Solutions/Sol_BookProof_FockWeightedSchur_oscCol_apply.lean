-- Prove2me | solution 1 for BookProof.FockWeightedSchur.oscCol_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:59:32.74787+00:00
-- url     : https://prove2.me/submissions/2e03cc70-46ad-4925-b6b5-f9d97fea1edb

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.oscCol_apply
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
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

theorem solution (k j : ℕ) : (oscCol k) j =
    if j = k + 1 then ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ)
    else if k = j + 1 then ((Real.sqrt (k : ℝ) : ℝ) : ℂ) else 0 := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [oscCol, if_pos rfl, Finsupp.single_apply]
    by_cases h : j = 0 + 1
    · rw [if_pos (by omega : (1:ℕ) = j), if_pos h]
      norm_num
    · rw [if_neg (by omega : ¬((1:ℕ) = j)), if_neg h, if_neg (by omega)]
  · rw [oscCol, if_neg (by omega), Finsupp.add_apply, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases h1 : j = k + 1
    · rw [if_pos (by omega : k + 1 = j), if_neg (by omega : ¬(k - 1 = j)), if_pos h1]
      simp
    · by_cases h2 : k = j + 1
      · rw [if_neg (by omega : ¬(k + 1 = j)), if_pos (by omega : k - 1 = j), if_neg h1,
          if_pos h2]
        simp
      · rw [if_neg (by omega : ¬(k + 1 = j)), if_neg (by omega : ¬(k - 1 = j)), if_neg h1,
          if_neg h2]
        simp
