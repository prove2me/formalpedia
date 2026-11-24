-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.trQsq_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:58.536805+00:00
-- url     : https://prove2.me/submissions/84c893ff-837a-4036-aff9-7ff9b293a2a6

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_trace_Qm_sq
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsNorm_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsNorm_le_of_sq
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_le_of_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {Dstar η0 e0 : ℝ} (hD : 0 < Dstar) (hη : -1 ≤ η0) (he : 0 ≤ e0)
    (hP : ∀ u u', u ≠ u' → hsSq (Kp B ga u u') ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar)
    (hK : ∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) :
    (Qm B ga * Qm B ga).trace.re ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d := by
  classical
  have hη' : 0 ≤ 1 + η0 := by linarith
  have hdiag : ∀ u, hsSq (Kp B ga u u) ≤ (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) := by
    intro u
    have h1 := hsSq_le_of_sub_one (d u) (Kd B ga u)
    have h2 := hsNorm_le_of_sq _ he (hK u)
    have hx := hsNorm_nonneg (Kd B ga u - 1)
    have hy := Real.sqrt_nonneg (d u : ℝ)
    have h3 : Real.sqrt (d u : ℝ) + hsNorm (Kd B ga u - 1)
        ≤ (1 + Real.sqrt e0) * Real.sqrt (d u : ℝ) := by linarith
    have h4 : 0 ≤ Real.sqrt (d u : ℝ) + hsNorm (Kd B ga u - 1) := by linarith
    have h5 : (Real.sqrt (d u : ℝ) + hsNorm (Kd B ga u - 1)) ^ 2
        ≤ ((1 + Real.sqrt e0) * Real.sqrt (d u : ℝ)) ^ 2 := by
      first
      | exact pow_le_pow_left₀ h4 h3 2
      | exact pow_le_pow_left h4 h3 2
      | nlinarith
    have h6 : ((1 + Real.sqrt e0) * Real.sqrt (d u : ℝ)) ^ 2 = (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    show hsSq (Kd B ga u) ≤ _
    linarith
  have hterm : ∀ u u', hsSq (Kp B ga u u')
      ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar
        + (if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0) := by
    intro u u'
    by_cases h : u = u'
    · rw [if_pos h]
      rw [← h]
      have h0 : 0 ≤ (1 + η0) * (d u : ℝ) * (d u : ℝ) / Dstar :=
        div_nonneg (mul_nonneg (mul_nonneg hη' (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) hD.le
      have := hdiag u
      linarith
    · rw [if_neg h, add_zero]
      exact hP u u' h
  have e1 : ∑ u, ∑ u', (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar = (1 + η0) * Rs d ^ 2 / Dstar := by
    unfold Rs
    simp only [sq, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
    ring
  have e2 : ∑ u, ∑ u', (if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0)
      = (1 + Real.sqrt e0) ^ 2 * Rs d := by
    unfold Rs
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    first
    | (rw [Finset.sum_ite_eq]; simp)
    | simp
  rw [trace_Qm_sq B ga hga, Complex.ofReal_re]
  calc ∑ u, ∑ u', hsSq (Kp B ga u u')
      ≤ ∑ u, ∑ u', ((1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar
        + (if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0)) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => hterm u u'
    _ = (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d := by
        simp only [Finset.sum_add_distrib]
        rw [e1, e2]
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
