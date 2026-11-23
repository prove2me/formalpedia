-- Prove2me | solution 1 for Formalism.ELL.N_additive_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:33.009042+00:00
-- url     : https://prove2.me/submissions/b6ced5e0-7482-4b19-9183-efd6bbaf73a9

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus
import Theorems.Thm_Formalism_ELL_EulerSeries_log_zero
import Theorems.Thm_Formalism_ELL_EulerSeries_log_add
import Theorems.Thm_Formalism_ELL_EulerSeries_integral_add_mul
import Theorems.Thm_Formalism_ELL_EulerSeries_exists_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL
namespace Formalism.ELL
theorem _root_.solution : Formalism.ELL.NAddSubgroup := by
  intro K _ _ _ σ
  classical
  refine ⟨⟨0, map_zero _, fun d => by simp, EulerSeries.log_zero.symm⟩, ?_, ?_⟩
  · rintro G H ⟨f, hf0, hfi, rfl⟩ ⟨g, hg0, hgi, rfl⟩
    exact ⟨f + g + f * g, by simp only [map_add, map_mul, hf0, hg0, add_zero, mul_zero],
      EulerSeries.integral_add_mul hfi hgi, EulerSeries.log_add hf0 hg0⟩
  · rintro G ⟨f, hf0, hfi, rfl⟩
    obtain ⟨h, hh0, hhi, hfh⟩ := EulerSeries.exists_inv hf0 hfi
    refine ⟨h, hh0, hhi, ?_⟩
    have := EulerSeries.log_add hf0 hh0
    rw [hfh, EulerSeries.log_zero] at this
    linear_combination -this
end Formalism.ELL
