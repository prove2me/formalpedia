-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.detPerturbNumeric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:35:25.408404+00:00
-- url     : https://prove2.me/submissions/355854ef-80c3-4779-afec-2662002ea152

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ParameterInequalities
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_DetMulEqSumPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset Matrix Polynomial
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : DetPerturbNumeric := by
  intro ρ hρ
  have hρ0 : (1:ℝ) ≤ ρ := by exact_mod_cast hρ
  have hpos : (0:ℝ) < ρ := by linarith
  have hx0 : 0 ≤ (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10 := by positivity
  have hρx : (ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ≤ 1 / 10 := by
    have e : (ρ:ℝ) * (ρ:ℝ) ^ (-(3:ℝ)/2) = (ρ:ℝ) ^ (-(1:ℝ)/2) := by
      rw [show (-(1:ℝ)/2) = 1 + (-(3:ℝ)/2) by norm_num, Real.rpow_add hpos, Real.rpow_one]
    have h1 : (ρ:ℝ) ^ (-(1:ℝ)/2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hρ0 (by norm_num)
    rw [mul_div_assoc', e]
    linarith
  have h1 : (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ
      ≤ Real.exp ((ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)]) ρ
  have h2 : Real.exp ((ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)) ≤ Real.exp (1/10) :=
    Real.exp_le_exp.2 hρx
  have h3 : Real.exp (1/10) ≤ 3/2 := by
    by_contra hc
    push_neg at hc
    have h4 : (3/2:ℝ)^10 < Real.exp (1/10) ^ 10 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    rw [← Real.exp_nat_mul] at h4
    norm_num at h4
    linarith [Real.exp_one_lt_d9]
  linarith
end Formalism.LatticeBaseChangeAlt
