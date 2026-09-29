-- Prove2me | solution 1 for BookProof.YangMillsGhost.ghostEnergy_empty
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T05:57:39.470063+00:00
-- url     : https://prove2.me/submissions/5591a4dd-8683-47b4-8f21-65731e4e0568

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

theorem solution (ω : Fin K → ℝ) : ghostEnergy ω (∅ : GConf K) = 0 := by
  simp [ghostEnergy]
