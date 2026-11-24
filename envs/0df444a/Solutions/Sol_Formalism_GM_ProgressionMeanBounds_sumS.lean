-- Prove2me | solution 1 for Formalism.GM.ProgressionMeanBounds.sumS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:32.934808+00:00
-- url     : https://prove2.me/submissions/86a94ad9-a92a-45ce-a3b7-3cb8345b2c3a

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
import Theorems.Thm_Formalism_GM_ProgressionMeanBounds_geom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Formalism.GM.ProgressionMeanBounds
open Finset Polynomial
namespace Formalism.GM.ProgressionMeanBounds
theorem _root_.solution (p : ℝ) (hp : 2 ≤ p) (Y₀ h : ℕ) :
    ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / p ^ i + 1) ≤ (Y₀ : ℝ) / (p - 1) + h := by
  have hp1 : 0 < p - 1 := by linarith
  have e : ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / p ^ i + 1) = (Y₀ : ℝ) * ∑ i ∈ Icc 1 h, (1 : ℝ) / p ^ i + h := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    · simp
  rw [e, geom p hp h]
  have hY : (0 : ℝ) ≤ Y₀ := Nat.cast_nonneg _
  have hq : 0 ≤ 1 / p ^ h := by positivity
  have : (Y₀ : ℝ) * ((1 - 1 / p ^ h) / (p - 1)) ≤ (Y₀ : ℝ) / (p - 1) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hp1]
    nlinarith
  linarith
end Formalism.GM.ProgressionMeanBounds
