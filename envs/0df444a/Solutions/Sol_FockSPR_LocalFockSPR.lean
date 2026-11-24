-- Prove2me | solution 1 for FockSPR.LocalFockSPR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:46.580173+00:00
-- url     : https://prove2.me/submissions/1d001ebc-5ebc-4775-972f-949d95578017

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_AnnulusLocalEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LeakageEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MainTheorem
public import Theorems.Thm_FockSPR_fock_space_coercivity
public import Theorems.Thm_FockSPR_fockNorm_eq_gaussian_integral


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex Real Finset Polynomial
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution
    (p : Polynomial ℂ)
    (hp : p.eval 0 = 0) :
    ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
    ≤ 4600 ^ 2 *
    ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2)
    := by
  by_cases hp0 : p = 0
  · simp_all
  · have hcoeff0 : p.coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero]; exact hp
    have hD : 1 ≤ p.natDegree := by
      by_contra hlt
      push Not at hlt
      interval_cases h : p.natDegree
      exact hp0 (eq_C_of_natDegree_eq_zero (by omega) |>.trans
        (by simp only [hcoeff0, map_zero]))
    set D := p.natDegree
    set a : Fin D → ℂ := fun k => p.coeff (k.val + 1)
    have heval : ∀ z, p.eval z = polyEval a z := by
      intro z
      rw [eval_eq_sum_range, polyEval]
      rw [Finset.sum_range_succ' (fun i => p.coeff i * z ^ i)]
      simp only [hcoeff0, zero_mul, pow_zero]
      rw [← Fin.sum_univ_eq_sum_range]
      ring
    simp_rw [heval, show ∀ z, |‖1 + polyEval a z‖ - 1| = rho (polyEval a z) from
      fun z => by simp only [rho]]
    have h1 := fockNorm_eq_gaussian_integral a
    have h2 := fock_space_coercivity hD a
    rw [← h1] at h2
    unfold rhoFockNormSq at h2
    rw [← mul_assoc, mul_comm (4600 ^ 2 : ℝ) (1 / Real.pi), mul_assoc] at h2
    exact le_of_mul_le_mul_left h2 (div_pos one_pos Real.pi_pos)
end FockSPR
