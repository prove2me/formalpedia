-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.fac_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:31.260423+00:00
-- url     : https://prove2.me/submissions/0d81ccc0-7893-4f27-b6c5-d1957991ecc3

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_E_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_E_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) :
    2 * (0.38:ℝ) ^ (n + 2) * ((n:ℝ) + 2) ^ n * Real.exp (1/4) ^ (n + 1) ≤ 4 ^ n * (n.factorial : ℝ) := by
  have hE := E_le
  have hE0 := E_pos
  have hf : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hx : (0:ℝ) ≤ (n:ℝ) + 2 := by positivity
  have h1 : ((n:ℝ) + 2) ^ n / (n.factorial : ℝ) ≤ Real.exp ((n:ℝ) + 2) := by
    first
    | exact Real.pow_div_factorial_le_exp _ hx n
    | exact Real.pow_div_factorial_le_exp hx n
  have h2 : ((n:ℝ) + 2) ^ n ≤ Real.exp ((n:ℝ) + 2) * (n.factorial : ℝ) := by
    first
    | (rwa [div_le_iff₀ hf] at h1)
    | (rwa [div_le_iff hf] at h1)
    | (have h1' := mul_le_mul_of_nonneg_right h1 hf.le
       rwa [div_mul_cancel₀ _ hf.ne'] at h1')
  have h3 : Real.exp ((n:ℝ) + 2) = Real.exp 1 ^ (n + 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hX : ((n:ℝ) + 2) ^ n ≤ (2.72:ℝ) ^ (n + 2) * (n.factorial : ℝ) := by
    calc ((n:ℝ) + 2) ^ n ≤ Real.exp ((n:ℝ) + 2) * (n.factorial : ℝ) := h2
      _ = Real.exp 1 ^ (n + 2) * (n.factorial : ℝ) := by rw [h3]
      _ ≤ (2.72:ℝ) ^ (n + 2) * (n.factorial : ℝ) := by
        have he1 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
        have he2 : Real.exp 1 ^ (n + 2) ≤ (2.72:ℝ) ^ (n + 2) := by
          first
          | exact pow_le_pow_left₀ (Real.exp_pos 1).le he1 (n + 2)
          | exact pow_le_pow_left (Real.exp_pos 1).le he1 (n + 2)
          | gcongr
        exact mul_le_mul_of_nonneg_right he2 hf.le
  have hEp : Real.exp (1/4) ^ (n + 1) ≤ (1.3:ℝ) ^ (n + 1) := by
    first
    | exact pow_le_pow_left₀ hE0.le hE (n + 1)
    | exact pow_le_pow_left hE0.le hE (n + 1)
    | gcongr
  have key : ∀ m : ℕ, 2 ≤ m →
      2 * (0.38:ℝ) ^ (m + 2) * (2.72:ℝ) ^ (m + 2) * (1.3:ℝ) ^ (m + 1) ≤ 4 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k _ ih =>
      have e1 : 2 * (0.38:ℝ) ^ (k + 1 + 2) * (2.72:ℝ) ^ (k + 1 + 2) * (1.3:ℝ) ^ (k + 1 + 1)
          = (0.38 * 2.72 * 1.3) * (2 * (0.38:ℝ) ^ (k + 2) * (2.72:ℝ) ^ (k + 2) * (1.3:ℝ) ^ (k + 1)) := by
        ring
      have e2 : (4:ℝ) ^ (k + 1) = 4 ^ k * 4 := pow_succ 4 k
      have h4 : (0:ℝ) < 4 ^ k := pow_pos (by norm_num) k
      rw [e1, e2]
      nlinarith
  have hQ := key n hn
  have hA : 0 ≤ 2 * (0.38:ℝ) ^ (n + 2) := by positivity
  have hY : 0 ≤ ((n:ℝ) + 2) ^ n := by positivity
  have hZ : 0 ≤ Real.exp (1/4) ^ (n + 1) := by positivity
  have hW : 0 ≤ (2.72:ℝ) ^ (n + 2) * (n.factorial : ℝ) := by positivity
  calc 2 * (0.38:ℝ) ^ (n + 2) * ((n:ℝ) + 2) ^ n * Real.exp (1/4) ^ (n + 1)
      ≤ 2 * (0.38:ℝ) ^ (n + 2) * ((2.72:ℝ) ^ (n + 2) * (n.factorial : ℝ)) * (1.3:ℝ) ^ (n + 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hX hA) hEp hZ
        exact mul_nonneg hA hW
    _ = (2 * (0.38:ℝ) ^ (n + 2) * (2.72:ℝ) ^ (n + 2) * (1.3:ℝ) ^ (n + 1)) * (n.factorial : ℝ) := by
        ring
    _ ≤ 4 ^ n * (n.factorial : ℝ) := mul_le_mul_of_nonneg_right hQ hf.le
end Formalism.FourierDecayAlt.P.Sz5
