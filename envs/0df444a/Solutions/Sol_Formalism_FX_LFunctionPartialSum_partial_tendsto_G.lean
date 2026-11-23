-- Prove2me | solution 1 for Formalism.FX.LFunctionPartialSum.partial_tendsto_G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:56.33737+00:00
-- url     : https://prove2.me/submissions/091d7638-ec0d-4da8-b031-192b9ba5d2ff

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_natCast_add_one_eq
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_summable_dterm
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_partial_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.FX.LFunctionPartialSum
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q) * (n : ℂ) ^ (-s)) atTop
      (𝓝 (G χ s)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have h1 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), dterm χ s n) atTop (𝓝 (G χ s)) :=
    ((summable_dterm χ hB hs).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M : ℕ => Ap χ M * ((M : ℂ) + 1) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hg : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (-s.re)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hs).comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have hg' := hg.const_mul B
    rw [mul_zero] at hg'
    refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_) hg'
    show ‖Ap χ M * ((M : ℂ) + 1) ^ (-s)‖ ≤ B * ((M : ℝ) + 1) ^ (-s.re)
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos hM, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB M) (Real.rpow_nonneg hM.le _)
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3.congr (partial_identity χ s)
end Formalism.FX.LFunctionPartialSum
