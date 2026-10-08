-- Prove2me | solution 1 for FlowCalculus.spatial_differential_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T14:52:17.557504+00:00
-- url     : https://prove2.me/submissions/7b4515d6-1bcb-431c-a4c5-059bc816de9e

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

open scoped ContDiff

set_option maxHeartbeats 800000

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (X : ℝ → E → E) (hX : ContDiff ℝ ∞ (fun p : ℝ × E => X p.1 p.2))
    (ψ : ℝ → E → E) (hψ : ContDiff ℝ ∞ (fun p : ℝ × E => ψ p.1 p.2))
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (t : ℝ) (y v : E) :
    HasDerivAt (fun s => fderiv ℝ (ψ s) y v)
      (fderiv ℝ (X t) (ψ t y) (fderiv ℝ (ψ t) y v)) t := by
  let P : ℝ × E → E := fun p => ψ p.1 p.2
  let A := fderiv ℝ (fderiv ℝ P) (t, y)
  have hP : Differentiable ℝ P := hψ.differentiable (by simp)
  have hA : HasFDerivAt (fderiv ℝ P) A (t, y) :=
    ((hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hrepr (s : ℝ) (z w : E) :
      fderiv ℝ (ψ s) z w = fderiv ℝ P (s, z) (0, w) := by
    have hh := (hP (s, z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right s z)
    have he := congrArg (fun L : E →L[ℝ] E => L w) hh.fderiv
    simpa [P, Function.comp_def] using he
  have htime (z : E) : fderiv ℝ P (t, z) (1, 0) = X t (ψ t z) := by
    have hh := (hP (t, z)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
    exact hh.unique (hflow t z)
  have hleft := (hA.comp y (hasFDerivAt_prodMk_right t y)).clm_apply
    (hasFDerivAt_const (1, (0 : E)) y)
  have heq : (fun z => fderiv ℝ P (t, z) (1, 0)) =
      (fun z => X t (ψ t z)) := funext htime
  change HasFDerivAt (fun z => fderiv ℝ P (t, z) (1, 0)) _ y at hleft
  rw [heq] at hleft
  have hXt : Differentiable ℝ (X t) :=
    (hX.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hψt : Differentiable ℝ (ψ t) :=
    (hψ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hright := (hXt (ψ t y)).hasFDerivAt.comp y (hψt y).hasFDerivAt
  have hval := congrArg (fun L : E →L[ℝ] E => L v) (hleft.unique hright)
  have hsym : A (1, 0) (0, v) = A (0, v) (1, 0) :=
    hψ.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top) (1, 0) (0, v)
  have hfirst := (hA.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))).clm_apply
      (hasDerivAt_const t (0, v))
  have hfinal : A (1, 0) (0, v) =
      fderiv ℝ (X t) (ψ t y) (fderiv ℝ (ψ t) y v) := by
    rw [hsym]
    simpa [ContinuousLinearMap.comp_apply] using hval
  have hh : HasDerivAt (fun s => fderiv ℝ P (s, y) (0, v)) (A (1, 0) (0, v)) t := by
    simpa [Function.comp_def] using hfirst
  exact (hh.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hrepr s y v)).congr_deriv hfinal
