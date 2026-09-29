-- Prove2me | solution 1 for BookProof.YangMillsGhost.ymGhostHam_preserves_ghostNumber
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:24.133497+00:00
-- url     : https://prove2.me/submissions/ab4b75d0-98ba-47f1-a3f6-2ebbc60310d5

-- Generated from ChapterYangMillsGhostSector.lean — solution of BookProof.YangMillsGhost.ymGhostHam_preserves_ghostNumber
import Mathlib
import Definitions.Def_ChapterYangMillsGhostSector
import Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_fibre
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
theorem solution (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ω : Fin K → ℝ)
    (n : ℕ) (x : ghostCore K)
    (hx : ∀ S : GConf K, ghostNum S ≠ n → (x : GhostSpace K) S = 0) :
    ∀ S : GConf K, ghostNum S ≠ n →
      ((ymGhostHam fabc ω x : GhostSpace K) : ∀ _ : GConf K, L2d 99) S = 0 := by

  intro S hS
  have hzero : (⟨(x : GhostSpace K) S, x.2.2 S⟩ : polyGaussCore (d := 99)) = 0 :=
    Subtype.ext (hx S hS)
  rw [ymGhostHam_fibre, hzero, map_zero]
