-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.gamma_integral_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:53:05.120841+00:00
-- url     : https://prove2.me/submissions/4be280bb-d1d5-4261-9c1b-86ded6118ee6

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_gamma_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset MeasureTheory
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution : GammaIntegralBound := by
  intro v g hv
  have hfun : (fun u : ℝ => Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g)
      = fun u => ∑ k ∈ range (g+1),
          (Real.pi * (g.choose k : ℝ) * (4 * v) ^ k) * (u ^ k * Real.exp (-Real.pi * u)) := by
    funext u
    rw [add_comm, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [one_pow, mul_one, mul_pow, mul_pow]
    ring
  have hint : ∀ k ∈ range (g+1), Integrable
      (fun u : ℝ => (Real.pi * (g.choose k : ℝ) * (4 * v) ^ k) * (u ^ k * Real.exp (-Real.pi * u)))
      (volume.restrict (Set.Ioi 0)) :=
    fun k _ => (gamma_term k).1.const_mul _
  rw [hfun]
  refine ⟨by unfold IntegrableOn; exact integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  have hpi := Real.pi_pos
  rw [add_comm (1:ℝ) (4 * (g:ℝ) * v / Real.pi), add_pow]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hkg : k ≤ g := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [integral_const_mul, (gamma_term k).2, one_pow, mul_one]
  have hf : (k.factorial : ℝ) ≤ (g : ℝ) ^ k := by
    exact_mod_cast (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hkg k)
  have e1 : Real.pi * (g.choose k : ℝ) * (4 * v) ^ k * ((k.factorial : ℝ) / Real.pi ^ (k+1))
      = (g.choose k : ℝ) * (4 * v / Real.pi) ^ k * (k.factorial : ℝ) := by
    have hpk : Real.pi ^ k ≠ 0 := by positivity
    rw [div_pow, pow_succ]
    field_simp
    try ring
  have e2 : (4 * (g:ℝ) * v / Real.pi) ^ k * (g.choose k : ℝ)
      = (g.choose k : ℝ) * (4 * v / Real.pi) ^ k * (g:ℝ) ^ k := by
    rw [show 4 * (g:ℝ) * v / Real.pi = (4 * v / Real.pi) * g by ring, mul_pow]
    ring
  rw [e1, e2]
  gcongr
end Formalism.LogVandermondeBounds.flipTwoThree
