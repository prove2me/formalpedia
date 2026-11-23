-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.attained
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:22.628648+00:00
-- url     : https://prove2.me/submissions/858aec49-730e-407d-8f52-c091828ee619

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_chebPt_eq

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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ChebAttained := by
  intro α β n hαβ hn
  have hd : 0 < β - α := by linarith
  have ha : (2 / (β - α)) ≠ 0 := by positivity
  intro W
  have hqe : (C (2 / (β - α)) * X - C ((α + β) / (β - α)) : ℝ[X]) =
      C (2 / (β - α)) * X + C (-((α + β) / (β - α))) := by
    rw [C_neg, sub_eq_add_neg]
  have hq : (C (2 / (β - α)) * X - C ((α + β) / (β - α)) : ℝ[X]).natDegree = 1 := by
    rw [hqe]; exact natDegree_linear ha
  have hl : (C (2 / (β - α)) * X - C ((α + β) / (β - α)) : ℝ[X]).leadingCoeff = 2 / (β - α) := by
    rw [hqe]; exact leadingCoeff_linear ha
  have hdeg : W.natDegree = n := by
    simp only [W, natDegree_comp, hq, Chebyshev.natDegree_T, Int.natAbs_natCast, mul_one]
  have hev : ∀ Y : ℝ, W.eval Y = (Chebyshev.T ℝ n).eval ((2 * Y - α - β) / (β - α)) := by
    intro Y
    simp only [W, eval_comp, eval_sub, eval_mul, eval_C, eval_X]
    congr 1; field_simp; ring
  refine ⟨hdeg, ?_, ?_, ?_⟩
  · have : W.coeff n = W.leadingCoeff := by rw [leadingCoeff, hdeg]
    rw [this]
    simp only [W]
    rw [leadingCoeff_comp (by rw [hq]; exact one_ne_zero), hl, Chebyshev.leadingCoeff_T,
      Chebyshev.natDegree_T, Int.natAbs_natCast]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, show (4:ℝ) / (β - α) = 2 * (2 / (β - α)) by ring, mul_pow, pow_succ (2:ℝ) m]
    ring
  · intro j
    rw [hev, chebPt_eq]
    have : (2 * ((α + β) / 2 + (β - α) / 2 * Chebyshev.node n j) - α - β) / (β - α)
        = Chebyshev.node n j := by field_simp; ring
    rw [this]
    exact Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt))
  · intro Y hY
    rw [hev]
    apply Chebyshev.abs_eval_T_real_le_one
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hd]; linarith [hY.1]
    · rw [div_le_iff₀ hd]; linarith [hY.2]
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
