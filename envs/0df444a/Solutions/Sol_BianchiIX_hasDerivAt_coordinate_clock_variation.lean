-- Prove2me | solution 1 for BianchiIX.hasDerivAt_coordinate_clock_variation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:32:52.505127+00:00
-- url     : https://prove2.me/submissions/c51d511d-e663-4aec-994e-e5a148d6ac62

import Theorems.Thm_BianchiIX_hasDerivAt_clock_projected_variation
import Theorems.Thm_BianchiIX_hasDerivAt_observable_variation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


/-- Coordinate variations at a fixed value of an observable clock, in the original time. -/
theorem solution
    {p : E → F} {clock rate : E → ℝ} {f : E → E} {field : ℝ × F → F}
    {alpha v : ℝ → E} {t : ℝ}
    (hp : ContDiffAt ℝ 2 p (alpha t)) (hc : ContDiffAt ℝ 2 clock (alpha t))
    (hf : DifferentiableAt ℝ f (alpha t)) (hr : DifferentiableAt ℝ rate (alpha t))
    (hfield : DifferentiableAt ℝ field (clock (alpha t), p (alpha t)))
    (ha : HasDerivAt alpha (f (alpha t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (alpha t) (v t)) t)
    (hclock : (fun x => fderiv ℝ clock x (f x)) =ᶠ[𝓝 (alpha t)] rate)
    (hstate : (fun x => fderiv ℝ p x (f x)) =ᶠ[𝓝 (alpha t)]
      (fun x => rate x • field (clock x, p x))) :
    HasDerivAt (fun s => fderiv ℝ p (alpha s) (v s) -
      fderiv ℝ clock (alpha s) (v s) • field (clock (alpha s), p (alpha s)))
      (rate (alpha t) • fderiv ℝ (fun Y => field (clock (alpha t), Y)) (p (alpha t))
        (fderiv ℝ p (alpha t) (v t) -
          fderiv ℝ clock (alpha t) (v t) • field (clock (alpha t), p (alpha t)))) t := by
  have hp' := (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hc' := (hc.differentiableAt (by norm_num)).hasFDerivAt
  have htheta : HasDerivAt (fun s => clock (alpha s)) (rate (alpha t)) t := by
    convert! hc'.comp_hasDerivAt t ha using 1
    exact hclock.self_of_nhds.symm
  have hY : HasDerivAt (fun s => p (alpha s))
      (rate (alpha t) • field (clock (alpha t), p (alpha t))) t := by
    convert! hp'.comp_hasDerivAt t ha using 1
    exact hstate.self_of_nhds.symm
  have hdtheta := hasDerivAt_observable_variation hc hf ha hv
  rw [hclock.fderiv_eq] at hdtheta
  have hproduct := hr.hasFDerivAt.smul (hfield.hasFDerivAt.comp (alpha t) (hc'.prodMk hp'))
  change HasFDerivAt (fun x => rate x • field (clock x, p x)) _ _ at hproduct
  have hdY : HasDerivAt (fun s => fderiv ℝ p (alpha s) (v s))
      (fderiv ℝ rate (alpha t) (v t) • field (clock (alpha t), p (alpha t)) +
        rate (alpha t) • fderiv ℝ field (clock (alpha t), p (alpha t))
          (fderiv ℝ clock (alpha t) (v t), fderiv ℝ p (alpha t) (v t))) t := by
    apply (hasDerivAt_observable_variation hp hf ha hv).congr_deriv
    rw [hstate.fderiv_eq, hproduct.fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, Function.comp_apply]
    exact add_comm _ _
  have H := hasDerivAt_clock_projected_variation hfield.hasFDerivAt htheta hY hdtheta hdY
  have hslice := hfield.hasFDerivAt.comp (p (alpha t))
    ((hasFDerivAt_const (clock (alpha t)) (p (alpha t))).prodMk (hasFDerivAt_id (p (alpha t))))
  change HasFDerivAt (fun Y => field (clock (alpha t), Y)) _ _ at hslice
  convert! H using 1
  rw [hslice.fderiv]
  rfl
