-- Prove2me | solution 1 for BianchiIX.abs_le_primitive_of_damping
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:56:03.604112+00:00
-- url     : https://prove2.me/submissions/0ccce77a-45ea-42fe-9605-2bff3135d07d

import Theorems.Thm_BianchiIX_abs_slope_right_le_of_damping
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


/-- An arbitrary signed damping coefficient contributes no growth beyond the forcing primitive. -/
theorem solution {f d g p p' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hdf : ∀ t ∈ Ico a b, HasDerivAt f (d t * f t + g t) t)
    (hp : ContinuousOn p (Icc a b)) (hdp : ∀ t ∈ Ico a b, HasDerivAt p (p' t) t)
    (hd : ∀ t ∈ Ico a b, d t ≤ 0) (hg : ∀ t ∈ Ico a b, |g t| ≤ p' t) :
    ∀ t ∈ Icc a b, |f t| ≤ |f a| + (p t - p a) := by
  intro t ht
  apply image_le_of_liminf_slope_right_le_deriv_boundary hf.abs (by simp) (continuousOn_const.add (hp.sub continuousOn_const))
    (fun s hs => ((hdp s hs).sub_const (p a)).const_add |f a| |>.hasDerivWithinAt) ?_ ht
  intro s hs r hr
  have H := abs_slope_right_le_of_damping (hdf s hs) (hd s hs) (hg s hs) hr
  simpa only [slope_def_module, smul_eq_mul] using H.frequently
