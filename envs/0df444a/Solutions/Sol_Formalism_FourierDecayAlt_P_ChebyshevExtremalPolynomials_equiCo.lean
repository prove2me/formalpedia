-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.equiCo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:00.480454+00:00
-- url     : https://prove2.me/submissions/70d98814-3481-45b0-aa34-3872f4afc41a

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_lagCo_affine
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_abs_lagCo_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
theorem _root_.solution : Formalism.FourierDecayAlt.F7.EquiCo := by
  intro n y₀ h hh
  have e : (fun i : Fin (n + 1) => y₀ + ((i:ℕ):ℝ) * h) =
      fun i : Fin (n + 1) => y₀ + h * ((i:ℕ):ℝ) := by
    funext i; ring
  rw [e]
  simp_rw [lagCo_affine, abs_mul, abs_lagCo_nat]
  rw [← mul_sum, abs_of_nonneg (by positivity)]
  have hs : ∑ j : Fin (n + 1), (((j:ℕ).factorial * (n - (j:ℕ)).factorial : ℝ))⁻¹ =
      2 ^ n / (n.factorial : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ((j.factorial * (n - j).factorial : ℝ))⁻¹) (n + 1)]
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [eq_div_iff hf, sum_mul]
    have := Nat.sum_range_choose n
    have h2 : ((∑ m ∈ range (n + 1), n.choose m : ℕ) : ℝ) = 2 ^ n := by rw [this]; push_cast; rfl
    rw [← h2]
    push_cast
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hc := Nat.choose_mul_factorial_mul_factorial hj'
    have hc' : (n.choose j : ℝ) * j.factorial * (n - j).factorial = n.factorial := by exact_mod_cast hc
    have h1 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    have h3 : ((n - j).factorial : ℝ) ≠ 0 := by exact_mod_cast (n - j).factorial_ne_zero
    rw [← hc']; field_simp
  rw [hs, div_pow, inv_pow]
  ring
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
