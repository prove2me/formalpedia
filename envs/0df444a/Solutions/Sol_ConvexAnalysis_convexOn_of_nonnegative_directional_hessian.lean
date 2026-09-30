-- Prove2me | solution 1 for ConvexAnalysis.convexOn_of_nonnegative_directional_hessian
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T00:11:39.751321+00:00
-- url     : https://prove2.me/submissions/682d4f57-fb27-4d95-b1cd-c7aa4f362b7d

import Mathlib.Tactic.Abel
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
open NormedSpace
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affine_line_first_second_hasDeriv (F : E → ℝ) (x v : E) (t : ℝ)
    (hc : ContDiffAt ℝ 2 F (x + t • v)) :
    let f : ℝ → ℝ := fun u => F (x + u • v)
    HasDerivAt f (fderiv ℝ F (x + t • v) v) t ∧
      HasDerivAt (deriv f) (fderiv ℝ (fun z => fderiv ℝ F z v) (x + t • v) v) t := by
  let P : ℝ → E := fun u => x + u • v
  let f : ℝ → ℝ := F ∘ P
  let D : E → ℝ := fun z => fderiv ℝ F z v
  have hP (u : ℝ) : HasDerivAt P v u := by
    have h := (hasDerivAt_const u x).add ((hasDerivAt_id u).smul_const v)
    change HasDerivAt P (0 + (1 : ℝ) • v) u at h
    simpa only [one_smul, zero_add] using h
  have hPc : Continuous P := continuous_const.add (continuous_id.smul continuous_const)
  have hf := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hP t)
  have hDc : ContDiffAt ℝ 1 D (P t) :=
    (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hd := hDc.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t (hP t)
  have heq : deriv f =ᶠ[nhds t] D ∘ P := by
    have hPt : Filter.Tendsto P (nhds t) (nhds (P t)) := hPc.continuousAt.tendsto
    filter_upwards [hPt.eventually (hc.eventually (by norm_num))] with u hu
    exact ((hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt u (hP u)).deriv
  exact ⟨hf, hd.congr_of_eventuallyEq heq⟩

theorem solution (F : E → ℝ) (U : Set E)
    (hU : Convex ℝ U) (hc : ∀ x ∈ U, ContDiffAt ℝ 2 F x)
    (hpos : ∀ x ∈ U, ∀ v : E, 0 ≤ fderiv ℝ (fun z => fderiv ℝ F z v) x v) :
    ConvexOn ℝ U F := by
  refine ⟨hU, ?_⟩
  intro x hx y hy a b ha hb hab
  let v := y - x
  let P : ℝ → E := fun t => x + t • v
  let f : ℝ → ℝ := F ∘ P
  have hPformula (t : ℝ) : P t = (1 - t) • x + t • y := by
    dsimp [P, v]
    rw [smul_sub, sub_smul, one_smul]
    abel
  have hPU : ∀ t ∈ Set.Icc (0 : ℝ) 1, P t ∈ U := by
    intro t ht
    rw [hPformula]
    exact hU hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :=
    affine_line_first_second_hasDeriv F x v t (hc _ (hPU t ht))
  have hfc : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f :=
    convexOn_of_deriv2_nonneg' (convex_Icc _ _)
      (fun t ht => (hderiv t ht).1.differentiableAt.differentiableWithinAt)
      (fun t ht => (hderiv t ht).2.differentiableAt.differentiableWithinAt)
      (fun t ht => by
        change 0 ≤ deriv (deriv f) t
        have he : deriv (deriv f) t =
            fderiv ℝ (fun z => fderiv ℝ F z v) (P t) v := (hderiv t ht).2.deriv
        rw [he]
        exact hpos _ (hPU t ht) v)
  have hh := hfc.2 (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) ha hb hab
  have hPb : P b = a • x + b • y := by
    rw [hPformula]
    have he : 1 - b = a := by linarith
    rw [he]
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, f, Function.comp_apply,
    hPb, P, zero_smul, add_zero, one_smul, v, add_sub_cancel] using hh
