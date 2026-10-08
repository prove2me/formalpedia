-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.qgFqQ_quadratic_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T23:15:03.467707+00:00
-- url     : https://prove2.me/submissions/88abd0a0-a6bd-4dc6-87c9-20073b3cc648

-- Generated from ChapterQg3DGaugeEsa.lean — solution of BookProof.Qg3DGaugeEsa.qgFqQ_quadratic_eq
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Theorems.Thm_BookProof_Qg3DGaugeEsa_sum_torsionVec_X
import Theorems.Thm_BookProof_Qg3DGaugeEsa_triple_swap
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
theorem solution :
    ∑ i : Fin 84, ∑ j : Fin 84, ((qgFqQ i j : ℝ) : ℂ)
        • ((X i : MvPolynomial (Fin 84) ℂ) * X j)
      = ((1 / 2 : ℝ) : ℂ) • ∑ m : Fin 64, torsionP m * torsionP m := by

  have hL : ∑ i : Fin 84, ∑ j : Fin 84, ((qgFqQ i j : ℝ) : ℂ)
        • ((X i : MvPolynomial (Fin 84) ℂ) * X j)
      = ∑ i : Fin 84, ∑ j : Fin 84, ∑ m : Fin 64,
          (((1 / 2 : ℝ) : ℂ) * ((torsionVec m i : ℝ) : ℂ) * ((torsionVec m j : ℝ) : ℂ))
            • ((X i : MvPolynomial (Fin 84) ℂ) * X j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hc : ((qgFqQ i j : ℝ) : ℂ)
        = ∑ m : Fin 64,
            (((1 / 2 : ℝ) : ℂ) * ((torsionVec m i : ℝ) : ℂ) * ((torsionVec m j : ℝ) : ℂ)) := by
      rw [qgFqQ]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hc, Finset.sum_smul]
  have hR : ((1 / 2 : ℝ) : ℂ) • ∑ m : Fin 64, torsionP m * torsionP m
      = ∑ m : Fin 64, ∑ i : Fin 84, ∑ j : Fin 84,
          (((1 / 2 : ℝ) : ℂ) * ((torsionVec m i : ℝ) : ℂ) * ((torsionVec m j : ℝ) : ℂ))
            • ((X i : MvPolynomial (Fin 84) ℂ) * X j) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← sum_torsionVec_X m, Finset.sum_mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, smul_smul]
    congr 1
    ring
  rw [hL, hR, triple_swap]
