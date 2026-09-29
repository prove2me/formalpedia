-- Prove2me | solution 1 for BookProof.YangMillsGhost.ghostEnergy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T05:57:40.517306+00:00
-- url     : https://prove2.me/submissions/34782dcb-8105-4758-8f02-db6c5561a9bc

import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Definitions.Def_ChapterYangMillsGhostSector

open BookProof.YangMillsGhost

variable {K : ℕ}

theorem solution {ω : Fin K → ℝ} (hω : ∀ p, 0 ≤ ω p) (S : GConf K) :
    0 ≤ ghostEnergy ω S := by
  simp only [ghostEnergy]
  exact Finset.sum_nonneg fun p _ => hω p
