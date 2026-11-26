-- Prove2me | solution 1 for Eden.spectrumInterpolation_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:25:44.453468+00:00
-- url     : https://prove2.me/submissions/52ce22b6-1f21-4939-b268-e47b6ff03843

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
import Theorems.Thm_Eden_spectrumInterpolation_eq_range
import Theorems.Thm_Eden_singularWeight_eq_one


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (a : Fin 5 → ℝ) :
    spectrumInterpolation a 5 = spectrumPartialSum a 5 := by
  rw [spectrumInterpolation_eq_range]
  apply Finset.sum_congr rfl
  intro i hi
  have h := singularWeight_eq_one (Finset.mem_range.mp hi) (le_refl (0 : ℝ))
  norm_num only [Nat.cast_ofNat, add_zero] at h
  rw [h, one_mul]
end Eden
