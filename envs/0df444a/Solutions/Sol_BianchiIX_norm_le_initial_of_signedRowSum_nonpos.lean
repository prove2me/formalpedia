-- Prove2me | solution 1 for BianchiIX.norm_le_initial_of_signedRowSum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:38:44.955257+00:00
-- url     : https://prove2.me/submissions/8dfe9e81-4532-4f3e-9e7a-d8057f6de451

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Theorems.Thm_BianchiIX_norm_slope_right_le_of_signedRowSum
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp


noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]


theorem solution {f : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivAt f ((A t).mulVec (f t)) t)
    (hA : ∀ t ∈ Ico a b, ∀ i, signedRowSum (A t) i ≤ 0) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ ‖f a‖ := by
  intro t ht
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (continuous_norm.comp_continuousOn hf) (le_refl ‖f a‖) continuousOn_const
    (fun x _ => hasDerivWithinAt_const x (Ici x) ‖f a‖) ?_ ht
  intro x hx r hr
  have H := norm_slope_right_le_of_signedRowSum (hderiv x hx) (hA x hx) (by simpa using hr)
  simpa only [slope_def_module, smul_eq_mul, Function.comp_apply] using H.frequently
