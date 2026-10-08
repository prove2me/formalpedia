-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.sum_torsionVec_X
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T23:00:36.099988+00:00
-- url     : https://prove2.me/submissions/e7dc415c-437a-4a28-b61b-59363d2e4fb7

-- Generated from ChapterQg3DGaugeEsa.lean — solution of BookProof.Qg3DGaugeEsa.sum_torsionVec_X
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Theorems.Thm_BookProof_Qg3DGaugeEsa_sum_single_X
open BookProof.Qg3DGaugeEsa




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (m : Fin 64) :
    ∑ i : Fin 84, ((torsionVec m i : ℝ) : ℂ) • (X i : MvPolynomial (Fin 84) ℂ)
      = torsionP m := by

  have hsplit : ∀ i : Fin 84, ((torsionVec m i : ℝ) : ℂ) • (X i : MvPolynomial (Fin 84) ℂ)
      = ((if i = torsionIdx1 m then (1 : ℝ) else 0 : ℝ) : ℂ) • (X i : MvPolynomial (Fin 84) ℂ)
        - ((if i = torsionIdx2 m then (1 : ℝ) else 0 : ℝ) : ℂ)
            • (X i : MvPolynomial (Fin 84) ℂ) := by
    intro i
    rw [← sub_smul]
    congr 1
    simp [torsionVec]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib, sum_single_X,
    sum_single_X]
  rfl
