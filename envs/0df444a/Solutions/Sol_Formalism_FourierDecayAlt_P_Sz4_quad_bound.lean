-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.quad_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:34.321892+00:00
-- url     : https://prove2.me/submissions/f52f27f0-b0f9-4599-bf20-31c96297c226

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_sum_pairs_reindex
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_sq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (J : ℕ) (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) :
    ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) ^ 2 ≤
      7 / 64 * (J : ℝ) := by
  rw [sum_pairs_reindex]
  calc _ ≤ ∑ d ∈ Ioc 0 J, (J : ℝ) / 16 * (1 / (d : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [mem_Ioc] at hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
        calc _ ≤ ∑ _i ∈ Icc 1 (J - d), (1 : ℝ) / 16 * (1 / (d : ℝ) ^ 2) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have e : ((i + d : ℕ) : ℝ) - (i : ℝ) = d := by push_cast; ring
              rw [e, div_pow, mul_pow]
              have h2 : (de (i + d) - de i) ^ 2 ≤ 1 := by
                rcases h01 (i + d) with a | a <;> rcases h01 i with b | b <;> rw [a, b] <;> norm_num
              rw [div_le_iff₀ (by positivity)]
              have e2 : (1 : ℝ) / 16 * (1 / (d : ℝ) ^ 2) * (4 ^ 2 * (d : ℝ) ^ 2) = 1 := by
                field_simp; norm_num
              rw [e2]; exact h2
          _ = ((J - d : ℕ) : ℝ) * ((1 : ℝ) / 16 * (1 / (d : ℝ) ^ 2)) := by simp
          _ ≤ (J : ℝ) * ((1 : ℝ) / 16 * (1 / (d : ℝ) ^ 2)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast Nat.sub_le J d
          _ = _ := by ring
    _ = (J : ℝ) / 16 * ∑ d ∈ Ioc 0 J, (1 : ℝ) / (d : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (J : ℝ) / 16 * (7 / 4) := mul_le_mul_of_nonneg_left (sq_sum J) (by positivity)
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.Sz4
