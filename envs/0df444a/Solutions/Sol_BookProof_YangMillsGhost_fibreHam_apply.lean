-- Prove2me | solution 1 for BookProof.YangMillsGhost.fibreHam_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:12.991752+00:00
-- url     : https://prove2.me/submissions/2aede248-b9d5-4b69-8db0-2d8d1f4ad9e9

-- Generated from ChapterYangMillsGhostSector.lean — solution of BookProof.YangMillsGhost.fibreHam_apply
import Mathlib
import Definitions.Def_ChapterYangMillsGhostSector
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.YangMillsGhost















noncomputable section

open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.YangMillsHermite
open BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

variable {K : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ω : Fin K → ℝ) (S : GConf K)
    (x : polyGaussCore (d := 99)) :
    fibreHam fabc ω S x
      = ymHamiltonian (coreRepPoly 99) fabc x + ((ghostEnergy ω S : ℝ) : ℂ) • (x : L2d 99) := rfl
