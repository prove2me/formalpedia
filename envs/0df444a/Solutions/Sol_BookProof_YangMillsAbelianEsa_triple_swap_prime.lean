-- Prove2me | solution 1 for BookProof.YangMillsAbelianEsa.triple_swap_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:34.512385+00:00
-- url     : https://prove2.me/submissions/299adc78-a000-4cda-a7dc-e30d2d512dfb

-- Generated from ChapterYangMillsAbelianEsa.lean — solution of BookProof.YangMillsAbelianEsa.triple_swap'
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
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
theorem solution {α : Type*} [AddCommMonoid α] {N D : ℕ} (F : Fin N → Fin D → Fin D → α) :
    ∑ i : Fin D, ∑ j : Fin D, ∑ m : Fin N, F m i j
      = ∑ m : Fin N, ∑ i : Fin D, ∑ j : Fin D, F m i j := by

  calc ∑ i : Fin D, ∑ j : Fin D, ∑ m : Fin N, F m i j
      = ∑ i : Fin D, ∑ m : Fin N, ∑ j : Fin D, F m i j :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ m : Fin N, ∑ i : Fin D, ∑ j : Fin D, F m i j := Finset.sum_comm
