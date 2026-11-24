-- Prove2me | solution 1 for Formalism.HF.P.tendsto_log_inv_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:12.169306+00:00
-- url     : https://prove2.me/submissions/5dc74c29-bf05-4486-a779-7b4e2da9c708

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution :
    Tendsto (fun x : ℝ => Real.log (1 / (x - 1))) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun x : ℝ => x - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => x - 1) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_sub_right (1:ℝ)).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x hx => mem_Ioi.2 (sub_pos.2 hx))
  have h2 := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1)
  refine h2.congr (fun x => ?_)
  simp only [Function.comp_apply, one_div, Real.log_inv]
end Formalism.HF.P
