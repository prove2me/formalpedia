-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.sum_ymMagVec_X
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:06:06.291518+00:00
-- url     : https://prove2.me/submissions/17430926-76c7-43ce-bfcf-151f15c35c0d

-- Generated from ChapterYangMillsAbelianEsa.lean — solution of BookProof.YangMillsAbelianEsa.sum_ymMagVec_X
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianEsa




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (m : Fin 24) :
    ∑ n : Fin 99, ((ymMagVec m n : ℝ) : ℂ) • (X n : MvPolynomial (Fin 99) ℂ)
      = magPoly 0 (decodeSpace m) (decodeColor m) := by

  have hmag : magPoly 0 (decodeSpace m) (decodeColor m)
      = ∑ j : Fin 3, ∑ k : Fin 3, ((levi (decodeSpace m) j k : ℝ) : ℂ)
          • (X (idxD j k (decodeColor m)) : MvPolynomial (Fin 99) ℂ) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp
  have hL : ∑ n : Fin 99, ((ymMagVec m n : ℝ) : ℂ) • (X n : MvPolynomial (Fin 99) ℂ)
      = ∑ n : Fin 99, ∑ j : Fin 3, ∑ k : Fin 3,
          ((if n = idxD j k (decodeColor m) then (levi (decodeSpace m) j k : ℝ) else 0 : ℝ) : ℂ)
            • (X n : MvPolynomial (Fin 99) ℂ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ymMagVec]
    push_cast
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_smul
  rw [hL, hmag]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single (idxD j k (decodeColor m))]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (idxD j k (decodeColor m))) h
