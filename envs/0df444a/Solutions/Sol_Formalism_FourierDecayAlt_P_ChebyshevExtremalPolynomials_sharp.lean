-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.sharp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:03.077986+00:00
-- url     : https://prove2.me/submissions/5ed8306d-5dd3-4471-8ee1-fc9c072d733d

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_chebPt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_nd_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_coValue
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_sum_half

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ChebSharp := by
  intro α β n hαβ hn
  have hd : 0 < β - α := by linarith
  constructor
  · intro i j hij
    rw [chebPt_eq, chebPt_eq] at hij
    have h2 : Chebyshev.node n i = Chebyshev.node n j := by
      have : (β - α) / 2 * Chebyshev.node n i = (β - α) / 2 * Chebyshev.node n j := by linarith
      exact mul_left_cancel₀ (by positivity) this
    exact nd_injective n h2
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hv : ∀ j : Fin (m + 2), |lagCo (Formalism.SA.C.chebPt α β (m + 1)) j| =
        (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) *
          (((2 : ℝ) ^ m / ((m:ℝ) + 1)) * (2 / (β - α)) ^ (m + 1)) := by
      intro j
      rw [coValue α β (m + 1) hαβ hn j, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul, Nat.add_sub_cancel]
      have h1 : |(if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1)| =
          (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) := by
        apply abs_of_nonneg; split_ifs <;> norm_num
      rw [h1, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      push_cast; ring
    rw [sum_congr rfl (fun j _ => hv j), ← sum_mul, sum_half]
    have hm : (m:ℝ) + 1 ≠ 0 := by positivity
    rw [show (4:ℝ) / (β - α) = 2 * (2 / (β - α)) by ring, mul_pow, pow_succ (2:ℝ) m]
    field_simp
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
