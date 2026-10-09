-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.qgSignedPoly_eq_fqPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:54:02.672506+00:00
-- url     : https://prove2.me/submissions/ba3ffa4a-41fc-41e8-abf6-1898ddb24154

-- Generated from ChapterQg3DGaugeEsa.lean — solution of BookProof.Qg3DGaugeEsa.qgSignedPoly_eq_fqPoly
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Theorems.Thm_BookProof_Qg3DGaugeEsa_qgFqQ_quadratic_eq
import Theorems.Thm_BookProof_Qg3DGaugeEsa_weylProd_self
import Theorems.Thm_BookProof_Qg3DGaugeEsa_qgSignedPoly_apply
import Theorems.Thm_BookProof_HermiteRelative_momPoly_eq_ymMomOp
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_mulXPoly_apply
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
theorem solution (kappa : Fin 84 → ℝ) :
    qgSignedPoly kappa = fqPoly (qgFqP kappa) qgFqQ 0 0 0 := by

  refine LinearMap.ext fun p => ?_
  have hfo : foPoly (d := 84) 0 0 p = 0 := by simp [foPoly]
  have hmom : ∑ i : Fin 84, ∑ j : Fin 84,
      ((qgFqP kappa i j : ℝ) : ℂ) • weylProd (momPoly i) (momPoly j) p
        = ∑ j : Fin 84, ((kappa j / 2 : ℝ) : ℂ) • pmom j (pmom j p) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [qgFqP, if_pos rfl, weylProd_self, momPoly_eq_ymMomOp]
    · intro b _ hb
      simp [qgFqP, Ne.symm hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hw : ∀ i j : Fin 84, weylProd (mulXPoly i) (mulXPoly j) p
      = ((X i : MvPolynomial (Fin 84) ℂ) * X j) * p := by
    intro i j
    simp only [weylProd, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
      mulXPoly_apply]
    rw [show (X i : MvPolynomial (Fin 84) ℂ) * (X j * p) = (X i * X j) * p by ring,
      show (X j : MvPolynomial (Fin 84) ℂ) * (X i * p) = (X i * X j) * p by ring,
      ← two_smul ℂ ((X i * X j : MvPolynomial (Fin 84) ℂ) * p), smul_smul]
    norm_num
  have hmul : ∑ i : Fin 84, ∑ j : Fin 84,
      ((qgFqQ i j : ℝ) : ℂ) • weylProd (mulXPoly i) (mulXPoly j) p
        = (((1 / 2 : ℝ) : ℂ) • ∑ m : Fin 64, torsionP m * torsionP m) * p := by
    calc ∑ i : Fin 84, ∑ j : Fin 84,
            ((qgFqQ i j : ℝ) : ℂ) • weylProd (mulXPoly i) (mulXPoly j) p
        = (∑ i : Fin 84, ∑ j : Fin 84,
            ((qgFqQ i j : ℝ) : ℂ) • ((X i : MvPolynomial (Fin 84) ℂ) * X j)) * p := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hw i j, smul_mul_assoc]
      _ = _ := by rw [qgFqQ_quadratic_eq]
  have hfq : fqPoly (qgFqP kappa) qgFqQ 0 0 0 p
      = (∑ i : Fin 84, ∑ j : Fin 84,
          ((qgFqP kappa i j : ℝ) : ℂ) • weylProd (momPoly i) (momPoly j) p)
        + ∑ i : Fin 84, ∑ j : Fin 84,
            ((qgFqQ i j : ℝ) : ℂ) • weylProd (mulXPoly i) (mulXPoly j) p := by
    rw [fqPoly, fqQuadPoly]
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Pi.zero_apply,
      Complex.ofReal_zero, zero_smul, add_zero, hfo]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  rw [qgSignedPoly_apply, hfq, hmom, hmul, smul_add]
  congr 1
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    congr 1
    push_cast
    ring
  · rw [Finset.smul_sum, smul_mul_assoc, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_assoc]
