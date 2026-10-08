-- Prove2me | solution 1 for ContactCalculus.lie_derivative_eq_exterior_on_regular_level
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:48:25.397951+00:00
-- url     : https://prove2.me/submissions/9c08e101-9e64-4b6f-af20-70b3ea168166

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_ImplicitCalculus_tangent_map_of_mapsTo_regular_level
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open GrayStability
open scoped ContDiff Topology

theorem solution {n c : ℕ} (F : E n → E c)
    (hF : ContDiff ℝ ∞ F) (η : OneForm n) (X : E n → E n)
    (hη : Differentiable ℝ η) (hX : Differentiable ℝ X)
    (hz : ∀ z ∈ levelSet F, η z (X z) = 0)
    (y : E n) (hy : y ∈ levelSet F)
    (hD : Function.Surjective (fderiv ℝ F y))
    (v : E n) (hv : v ∈ tangentSpace F y) :
    lieDerivOneForm X η y v = extDerivOneForm η y (X y) v := by
  let g : E n → ℝ := fun z => η z (X z)
  have hd := (hη y).hasFDerivAt.clm_apply (hX y).hasFDerivAt
  have hzero := ImplicitCalculus.tangent_map_of_mapsTo_regular_level
    F (fderiv ℝ F y) y v (hF.hasStrictFDerivAt (by simp)) hD hv
    g (id : ℝ → ℝ) hd.differentiableAt differentiableAt_id
    (Filter.Eventually.of_forall (fun z hzy => by
      have hzM : z ∈ levelSet F := hzy.trans hy
      change η z (X z) = η y (X y)
      rw [hz z hzM, hz y hy]))
  have hgzero : fderiv ℝ g y v = 0 := by simpa using hzero
  have he := congrArg (fun L : E n →L[ℝ] ℝ => L v) hd.fderiv
  change fderiv ℝ g y v = _ at he
  rw [hgzero] at he
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply] at he
  unfold lieDerivOneForm extDerivOneForm
  linarith
