-- Prove2me | solution 1 for Formalism.IncomingBounds.constantIdentities
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:11.269268+00:00
-- url     : https://prove2.me/submissions/bf301618-ae23-45ba-8c37-05dface26d88

import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : Constants := by
  intro l hl
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have hA : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hB : 0 < (l : ℝ) - 1 := by linarith
  have hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1 := mul_one_div_cancel hA.ne'
  have hr : ((l : ℝ) - 1) * (1 / ((l : ℝ) - 1)) = 1 := mul_one_div_cancel hB.ne'
  have hl1 : (l : ℝ) * (l : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have hl2 : (l : ℝ) ^ 2 * ((l : ℝ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hl0)
  refine ⟨?_, ?_⟩
  · have hu0 : (0 : ℝ) ≤ ((l : ℝ) ^ 2)⁻¹ := by positivity
    have hu1 : ((l : ℝ) ^ 2)⁻¹ < 1 := by
      nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ (l : ℝ) ^ 2 - 4) hu0]
    have hg := (hasSum_geometric_of_lt_one hu0 hu1).mul_left ((l : ℝ)⁻¹)
    have hf : (fun k : ℕ => ((l : ℝ) ^ (2 * k + 1))⁻¹) = fun k : ℕ => (l : ℝ)⁻¹ * ((l : ℝ) ^ 2)⁻¹ ^ k := by
      funext k
      rw [pow_succ, pow_mul, mul_inv, ← inv_pow, mul_comm]
    have hu : (1 : ℝ) - ((l : ℝ) ^ 2)⁻¹ = ((l : ℝ) ^ 2 - 1) * ((l : ℝ) ^ 2)⁻¹ := by
      linear_combination (-1 : ℝ) * hl2
    have hv : gam l = (l : ℝ)⁻¹ * (1 - ((l : ℝ) ^ 2)⁻¹)⁻¹ := by
      rw [gam, hu, mul_inv, inv_inv]
      linear_combination (-((l : ℝ) * ((l : ℝ) ^ 2 - 1)⁻¹)) * hl1
    rw [hf, hv]
    exact hg
  · unfold rho gam
    linear_combination (1 / ((l : ℝ) - 1)) * hq - ((l : ℝ) + 1) * (1 / ((l : ℝ) ^ 2 - 1)) * hr
end Formalism.IncomingBounds
