-- Prove2me | solution 1 for BookProof.QgOuterFock.qgSectorPoly_eq_sum_particles
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:46:36.385822+00:00
-- url     : https://prove2.me/submissions/6bf6fefd-8c94-4882-ba57-ab3e2c7d8f8a

-- Generated from ChapterQgOuterFockEsa.lean — solution of BookProof.QgOuterFock.qgSectorPoly_eq_sum_particles
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
import Theorems.Thm_BookProof_QgOuterFock_qgKappaN_pcoord
import Theorems.Thm_BookProof_QgOuterFock_sum_reindex_particles
import Theorems.Thm_BookProof_QgOuterFock_linForm_qgTorsionVecN
import Definitions.Def_ChapterGaugeMechanicsCharge
import Definitions.Def_ChapterYangMillsHermite
open BookProof
open BookProof.ChapterGaugeMechanicsCharge
open BookProof.QgOuterFock




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.Qg3DGaugeEsa
open BookProof.QgHermiteOscillator
open BookProof.DirectSumEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    sqSumPoly (qgKappaN n) (qgTorsionVecN n)
      = ((1 / 2 : ℝ) : ℂ) • ∑ p : Fin n,
          ((∑ j : Fin 84, ((qgKappa j : ℝ) : ℂ) •
              (YangMillsHermite.momOp (pcoord p j)).comp (YangMillsHermite.momOp (pcoord p j)))
            + ∑ m : Fin 64, (YangMillsHermite.mulOp (qgTorsionBlock p m)).comp
                (YangMillsHermite.mulOp (qgTorsionBlock p m))) := by

  rw [sqSumPoly, Finset.sum_add_distrib]
  congr 2
  · rw [sum_reindex_particles]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => by
      rw [qgKappaN_pcoord]
  · rw [Fintype.sum_prod_type (fun r : Fin n × Fin 64 =>
      (YangMillsHermite.mulOp (linForm (qgTorsionVecN n r))).comp
        (YangMillsHermite.mulOp (linForm (qgTorsionVecN n r))))]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun m _ => by
      rw [linForm_qgTorsionVecN p m]
      rfl
