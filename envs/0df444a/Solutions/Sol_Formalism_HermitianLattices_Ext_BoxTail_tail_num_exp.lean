-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_num_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:50.402487+00:00
-- url     : https://prove2.me/submissions/076c4b01-cc0d-4681-8493-8b5cddf88450

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailNum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (ε K : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop, K * (x ^ 404 * Real.exp (-(x ^ (ε / 6)))) ≤ 1 / 3 := by
  have hs : 0 < ε / 6 := by positivity
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ (ε / 6)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hs
  have h2 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (404 / (ε / 6)) 1 one_pos).comp h1
  have hc : ε / 6 * (404 / (ε / 6)) = (404 : ℝ) := by field_simp
  have h3 : Filter.Tendsto (fun x : ℝ => x ^ 404 * Real.exp (-(x ^ (ε / 6))))
      Filter.atTop (nhds 0) := by
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    simp only [Function.comp, neg_mul, one_mul]
    rw [← Real.rpow_mul hx.le, hc]
    congr 1
    exact_mod_cast Real.rpow_natCast x 404
  have h4 : Filter.Tendsto (fun x : ℝ => K * (x ^ 404 * Real.exp (-(x ^ (ε / 6)))))
      Filter.atTop (nhds 0) := by
    simpa using h3.const_mul K
  exact h4.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))
end Formalism.HermitianLattices.Ext.BoxTail
