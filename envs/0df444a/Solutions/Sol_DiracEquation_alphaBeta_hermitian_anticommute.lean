-- Prove2me | solution 1 for DiracEquation.alphaBeta_hermitian_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:21:28.922051+00:00
-- url     : https://prove2.me/submissions/848f779a-4d1a-464e-ba88-6fb2a942cbad

import Definitions.Def_DiracEquation_fields

open DiracEquation

namespace Ag1Aux_DiracAB

set_option maxHeartbeats 3000000 in
theorem gamma_family : IsGammaFamily gammaDirac := by
  intro mu nu
  fin_cases mu <;> fin_cases nu <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gammaDirac, eta, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring_nf <;>
    simp

theorem g0_herm : (gammaDirac 0).conjTranspose = gammaDirac 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gammaDirac, Matrix.conjTranspose_apply]

theorem gk_antiherm (k : Fin 3) : (gammaDirac k.succ).conjTranspose = -gammaDirac k.succ := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gammaDirac, Matrix.conjTranspose_apply]

theorem sq_gen (a : Fin 4) (c : ℂ) (he : eta a a = c) :
    gammaDirac a * gammaDirac a = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h := gamma_family a a
  rw [he] at h
  have h2 : (2 : ℂ) • (gammaDirac a * gammaDirac a) = (2 : ℂ) • (c • (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    rw [two_smul, h, smul_smul]
  exact smul_right_injective _ (two_ne_zero (α := ℂ)) h2

theorem sq0 : gammaDirac 0 * gammaDirac 0 = 1 := by
  rw [sq_gen 0 1 (by simp [eta]), one_smul]

theorem sqk (k : Fin 3) : gammaDirac k.succ * gammaDirac k.succ = -1 := by
  rw [sq_gen k.succ (-1) (by simp [eta, Fin.succ_ne_zero]), neg_one_smul]

theorem anti (a b : Fin 4) (hab : a ≠ b) : gammaDirac a * gammaDirac b = -(gammaDirac b * gammaDirac a) := by
  have h := gamma_family a b
  have he : eta a b = 0 := by simp [eta, hab]
  rw [he, mul_zero, zero_smul] at h
  exact eq_neg_of_add_eq_zero_left h

end Ag1Aux_DiracAB

open Ag1Aux_DiracAB

theorem solution :
    betaDirac.conjTranspose = betaDirac ∧
    betaDirac * betaDirac = 1 ∧
    (∀ i : Fin 3, (alphaDirac i).conjTranspose = alphaDirac i) ∧
    (∀ i : Fin 3, alphaDirac i * alphaDirac i = 1) ∧
    (∀ i j : Fin 3, i ≠ j → alphaDirac i * alphaDirac j + alphaDirac j * alphaDirac i = 0) ∧
    (∀ i : Fin 3, alphaDirac i * betaDirac + betaDirac * alphaDirac i = 0) := by
  refine ⟨g0_herm, sq0, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [alphaDirac, Matrix.conjTranspose_mul, g0_herm, gk_antiherm]
    rw [neg_mul, anti _ _ (Fin.succ_ne_zero i), neg_neg]
  · intro i
    simp only [alphaDirac]
    calc gammaDirac 0 * gammaDirac i.succ * (gammaDirac 0 * gammaDirac i.succ) = gammaDirac 0 * (gammaDirac i.succ * gammaDirac 0) * gammaDirac i.succ := by
          simp only [mul_assoc]
      _ = gammaDirac 0 * (-(gammaDirac 0 * gammaDirac i.succ)) * gammaDirac i.succ := by rw [anti _ _ (Fin.succ_ne_zero i)]
      _ = -((gammaDirac 0 * gammaDirac 0) * (gammaDirac i.succ * gammaDirac i.succ)) := by noncomm_ring
      _ = 1 := by rw [sq0, sqk]; simp
  · intro i j hij
    simp only [alphaDirac]
    have hs : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective _ h)
    calc gammaDirac 0 * gammaDirac i.succ * (gammaDirac 0 * gammaDirac j.succ) + gammaDirac 0 * gammaDirac j.succ * (gammaDirac 0 * gammaDirac i.succ)
        = gammaDirac 0 * (gammaDirac i.succ * gammaDirac 0) * gammaDirac j.succ + gammaDirac 0 * (gammaDirac j.succ * gammaDirac 0) * gammaDirac i.succ := by
          simp only [mul_assoc]
      _ = gammaDirac 0 * (-(gammaDirac 0 * gammaDirac i.succ)) * gammaDirac j.succ + gammaDirac 0 * (-(gammaDirac 0 * gammaDirac j.succ)) * gammaDirac i.succ := by
          rw [anti _ _ (Fin.succ_ne_zero i), anti _ _ (Fin.succ_ne_zero j)]
      _ = -((gammaDirac 0 * gammaDirac 0) * (gammaDirac i.succ * gammaDirac j.succ + gammaDirac j.succ * gammaDirac i.succ)) := by noncomm_ring
      _ = 0 := by rw [sq0, anti _ _ hs]; simp
  · intro i
    simp only [alphaDirac, betaDirac]
    calc gammaDirac 0 * gammaDirac i.succ * gammaDirac 0 + gammaDirac 0 * (gammaDirac 0 * gammaDirac i.succ)
        = gammaDirac 0 * (gammaDirac i.succ * gammaDirac 0) + gammaDirac 0 * (gammaDirac 0 * gammaDirac i.succ) := by simp only [mul_assoc]
      _ = gammaDirac 0 * (-(gammaDirac 0 * gammaDirac i.succ)) + gammaDirac 0 * (gammaDirac 0 * gammaDirac i.succ) := by
          rw [anti _ _ (Fin.succ_ne_zero i)]
      _ = 0 := by noncomm_ring
