-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.prod_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:33.62986+00:00
-- url     : https://prove2.me/submissions/5ddcbefe-7241-43a1-8ca1-7a1fcf3b5e0c

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_abs_log_one_sub_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_geom_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_inv_pow_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution (q : ℕ) (hq : 2 ≤ q) (k n : ℕ) :
    0 < ∏ j ∈ Ioc k n, (1 - ((q : ℝ) ^ j)⁻¹) ∧
      |Real.log (∏ j ∈ Ioc k n, (1 - ((q : ℝ) ^ j)⁻¹))| ≤ 2 / 2 ^ k := by
  have hpos : ∀ j ∈ Ioc k n, 0 < 1 - ((q : ℝ) ^ j)⁻¹ := by
    intro j hj
    have hj1 : 1 ≤ j := by have := (mem_Ioc.mp hj).1; omega
    obtain ⟨_, h2, h3⟩ := inv_pow_bounds q j hq hj1
    linarith
  refine ⟨prod_pos hpos, ?_⟩
  rw [Real.log_prod (fun j hj => (hpos j hj).ne')]
  calc |∑ j ∈ Ioc k n, Real.log (1 - ((q : ℝ) ^ j)⁻¹)|
      ≤ ∑ j ∈ Ioc k n, |Real.log (1 - ((q : ℝ) ^ j)⁻¹)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Ioc k n, 2 * (1 / (2 : ℝ) ^ j) := by
        apply sum_le_sum
        intro j hj
        have hj1 : 1 ≤ j := by have := (mem_Ioc.mp hj).1; omega
        obtain ⟨h1, h2, h3⟩ := inv_pow_bounds q j hq hj1
        have := abs_log_one_sub_le h1 (h2.trans h3)
        linarith
    _ = 2 * ∑ j ∈ Ioc k n, 1 / (2 : ℝ) ^ j := by rw [mul_sum]
    _ ≤ 2 * (1 / 2 ^ k) := by
        have := geom_le k n
        linarith
    _ = 2 / 2 ^ k := by ring
end Formalism.FourierDecayAlt.P.Sz2
