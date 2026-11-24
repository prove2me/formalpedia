-- Prove2me | solution 1 for Formalism.ZRN.e_crude
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:10.943859+00:00
-- url     : https://prove2.me/submissions/e6a62985-50ba-4488-aa29-af36209d6e22

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Theorems.Thm_Formalism_ZRN_norm_cpow_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖e n s‖ ≤ ‖1 - s‖ + 2 * ((n : ℝ) + 1) + 1 := by
  have h1 := norm_cpow_nat n 1 (by positivity) (-s)
  have h2 := norm_cpow_nat n 1 (by positivity) (1 - s)
  have h3 := norm_cpow_nat n 2 (by positivity) (1 - s)
  push_cast at h1 h2 h3
  have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
  have b1 : ((n : ℝ) + 1) ^ (-s).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by simp; linarith)
  have b2 : ((n : ℝ) + 1) ^ (1 - s).re ≤ (n : ℝ) + 1 := by
    calc ((n : ℝ) + 1) ^ (1 - s).re ≤ ((n : ℝ) + 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by simp; linarith)
      _ = (n : ℝ) + 1 := Real.rpow_one _
  have b3 : ((n : ℝ) + 2) ^ (1 - s).re ≤ (n : ℝ) + 2 := by
    calc ((n : ℝ) + 2) ^ (1 - s).re ≤ ((n : ℝ) + 2) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp; linarith)
      _ = (n : ℝ) + 2 := Real.rpow_one _
  unfold e
  calc ‖(1 - s) * ((n : ℂ) + 1) ^ (-s) + ((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s)‖
      ≤ ‖(1 - s) * ((n : ℂ) + 1) ^ (-s)‖ + ‖((n : ℂ) + 1) ^ (1 - s)‖
          + ‖((n : ℂ) + 2) ^ (1 - s)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖1 - s‖ * 1 + ((n : ℝ) + 1) + ((n : ℝ) + 2) := by
        rw [norm_mul, h1, h2, h3]
        gcongr
    _ = ‖1 - s‖ + 2 * ((n : ℝ) + 1) + 1 := by ring
end Formalism.ZRN
