-- Prove2me | solution 1 for BookProof.YangMillsGhost.fibreHam_abelian_esa
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:35:36.470372+00:00
-- url     : https://prove2.me/submissions/13a5acd3-86a7-495e-9df3-15017f184c51
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterYangMillsGhostSector.lean — solution of BookProof.YangMillsGhost.fibreHam_abelian_esa
import Mathlib
import Definitions.Def_ChapterYangMillsGhostSector
import Theorems.Thm_BookProof_KatoRellich_essentiallySelfAdjointOn_add_bounded
import Theorems.Thm_BookProof_YangMillsAbelianEsa_ymAbelian_essentiallySelfAdjointOn_core
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn
open BookProof.YangMillsGhost




noncomputable section

open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.YangMillsHermite BookProof.YangMillsAbelianEsa
open BookProof.KatoRellich BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

variable {K : ℕ}

variable {K : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (ω : Fin K → ℝ) (S : GConf K) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 99)) (fibreHam 0 ω S) :=
  essentiallySelfAdjointOn_add_bounded _ (ymHamiltonian_symmetricOn (coreRepPoly 99) 0)
      ymAbelian_essentiallySelfAdjointOn_core
      (((ghostEnergy ω S : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (L2d 99))
      (fun u v => by
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
          inner_smul_left, inner_smul_right, Complex.conj_ofReal])
