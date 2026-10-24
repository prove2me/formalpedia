-- Prove2me | solution 1 for FunctionalInequalities.Analysis.lipschitzWith_gradient_of_second_difference_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:21:47.643684+00:00
-- url     : https://prove2.me/submissions/25e9a0c7-c9b6-4303-a62a-f04b7b9c9537

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section W0T4SecondDifferenceLipschitz
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **A second-difference bound gives a Lipschitz gradient**: a differentiable convex function with
`u(x + h) + u(x − h) − 2 u(x) ≤ C ‖h‖²` for all `x, h` has a `4C`-Lipschitz gradient. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {u : E → ℝ} {C : ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) (hC : 0 ≤ C)
    (hsd : ∀ x h : E, u (x + h) + u (x - h) - 2 * u x ≤ C * ‖h‖ ^ 2) :
    LipschitzWith (Real.toNNReal (4 * C)) (gradient u) := by
  have hlineconv (x h : E) :
      ConvexOn ℝ Set.univ (u ∘ fun t : ℝ => x + t • h) := by
    refine ⟨convex_univ, ?_⟩
    intro a _ha b _hb p q hp hq hpq
    have hu := hconv.2 (x := x + a • h) (y := x + b • h)
      (Set.mem_univ _) (Set.mem_univ _) hp hq hpq
    have heq :
        p • (x + a • h) + q • (x + b • h) =
          x + (p • a + q • b) • h := by
      calc
        p • (x + a • h) + q • (x + b • h) =
            (p + q) • x + (p • a + q • b) • h := by
              module
        _ = x + (p • a + q • b) • h := by
          rw [hpq, one_smul]
    rw [heq] at hu
    simpa only [Function.comp_apply] using hu
  have hfirst (x h : E) :
      inner ℝ (gradient u x) h ≤ u (x + h) - u x := by
    have hld₀ :=
      ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const h).const_add x
    have hld : HasDerivAt (fun t : ℝ => x + t • h) h 0 := by
      simpa only [id_eq, one_smul ℝ h] using hld₀
    have hu0 :
        HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • h) := by
      simpa only [zero_smul, add_zero] using
        (hdiff (x + (0 : ℝ) • h)).hasFDerivAt
    have hcomp := hu0.comp_hasDerivAt (0 : ℝ) hld
    have hderiv :
        deriv (u ∘ fun t : ℝ => x + t • h) 0 =
          inner ℝ (gradient u x) h := by
      rw [hcomp.deriv]
      change (fderiv ℝ u x) h =
        inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) h
      simp only [InnerProductSpace.toDual_symm_apply]
    have hm :=
      (hlineconv x h).deriv_le_slope (x := 0) (y := 1)
        (Set.mem_univ _) (Set.mem_univ _) (by norm_num) hcomp.differentiableAt
    rw [hderiv] at hm
    simpa [slope, Function.comp_def] using hm
  have hupper (x h : E) :
      u (x + h) - u x - inner ℝ (gradient u x) h ≤ C * ‖h‖ ^ 2 := by
    have hh := hfirst x (-h)
    have hh' :
        -inner ℝ (gradient u x) h ≤ u (x - h) - u x := by
      simpa [sub_eq_add_neg] using hh
    linarith [hsd x h, hh']
  by_cases hCzero : C = 0
  · have heq0 (x h : E) :
        u (x + h) = u x + inner ℝ (gradient u x) h := by
      have hl := hfirst x h
      have hu := hupper x h
      have hu' :
          u (x + h) - u x - inner ℝ (gradient u x) h ≤ 0 := by
        rw [hCzero, zero_mul] at hu
        exact hu
      linarith only [hl, hu']
    have haff (x z : E) :
        u z = u x + inner ℝ (gradient u x) (z - x) := by
      have hh := heq0 x (z - x)
      have hx : x + (z - x) = z := by
        abel
      rw [hx] at hh
      exact hh
    have hinner (x y h : E) :
        inner ℝ (gradient u x) h = inner ℝ (gradient u y) h := by
      have e₁ := haff x (x + h)
      have hx : (x + h) - x = h := by
        abel
      rw [hx] at e₁
      have e₂ := haff y (x + h)
      have hxy : (x + h) - y = (x - y) + h := by
        abel
      rw [hxy, inner_add_right] at e₂
      have e₃ := haff x y
      have e₃' :
          u y = u x - inner ℝ (gradient u x) (x - y) := by
        calc
          u y = u x + inner ℝ (gradient u x) (y - x) := e₃
          _ = u x - inner ℝ (gradient u x) (x - y) := by
            rw [show y - x = -(x - y) by abel]
            rw [inner_neg_right]
            ring
      have e₄ := haff y x
      have hdir :
          inner ℝ (gradient u x) (x - y) =
            inner ℝ (gradient u y) (x - y) := by
        have hax :
            inner ℝ (gradient u x) (x - y) = u x - u y := by
          calc
            inner ℝ (gradient u x) (x - y) =
                u x - (u x - inner ℝ (gradient u x) (x - y)) := by
                  ring
            _ = u x - u y := by rw [← e₃']
        have hbx :
            inner ℝ (gradient u y) (x - y) = u x - u y := by
          calc
            inner ℝ (gradient u y) (x - y) =
                (u y + inner ℝ (gradient u y) (x - y)) - u y := by
                  ring
            _ = u x - u y := by rw [e₄]
        exact hax.trans hbx.symm
      have e₂' :
          u (x + h) =
            u x - inner ℝ (gradient u x) (x - y) +
              (inner ℝ (gradient u x) (x - y) +
                inner ℝ (gradient u y) h) := by
        rw [e₃'] at e₂
        rw [← hdir] at e₂
        exact e₂
      have e₂'' :
          u x + inner ℝ (gradient u x) h =
            u x + inner ℝ (gradient u y) h := by
        calc
          u x + inner ℝ (gradient u x) h = u (x + h) := by
            exact e₁.symm
          _ = u x - inner ℝ (gradient u x) (x - y) +
              (inner ℝ (gradient u x) (x - y) +
                inner ℝ (gradient u y) h) := e₂'
          _ = u x + inner ℝ (gradient u y) h := by
            ring
      exact add_left_cancel e₂''
    have hgrad_eq (x y : E) : gradient u x = gradient u y := by
      have hh := hinner x y (gradient u x - gradient u y)
      have hz :
          inner ℝ (gradient u x - gradient u y)
              (gradient u x - gradient u y) = 0 := by
        calc
          inner ℝ (gradient u x - gradient u y)
              (gradient u x - gradient u y) =
              inner ℝ (gradient u x) (gradient u x - gradient u y) -
                inner ℝ (gradient u y) (gradient u x - gradient u y) := by
                  rw [inner_sub_left]
          _ = 0 := sub_eq_zero.mpr hh
      let v : E := gradient u x - gradient u y
      have hz' : inner ℝ v v = 0 := by
        exact hz
      have hn : ‖v‖ ^ 2 = 0 := by
        calc
          ‖v‖ ^ 2 = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
          _ = 0 := hz'
      have hzero : v = 0 :=
        norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
      exact sub_eq_zero.mp hzero
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    rw [hgrad_eq x y]
    simp [hCzero]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hcoercive (x y : E) :
        ‖gradient u x - gradient u y‖ ^ 2 ≤
          4 * C * inner ℝ (gradient u x - gradient u y) (x - y) := by
      let d : E := gradient u x - gradient u y
      let t : ℝ := (2 * C)⁻¹
      let z : E := y + t • d
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have hmin := hfirst x (z - x)
      have hmin' :
          inner ℝ (gradient u x) (y - x) +
              inner ℝ (gradient u x) (t • d) ≤ u z - u x := by
        have hz : x + (z - x) = z := by
          abel
        rw [hz] at hmin
        have hz' : z - x = (y - x) + t • d := by
          dsimp [z]
          abel
        rw [hz', inner_add_right] at hmin
        exact hmin
      have hu :
          u z - u y - inner ℝ (gradient u y) (t • d) ≤
            C * ‖t • d‖ ^ 2 := by
        change u (y + t • d) - u y - inner ℝ (gradient u y) (t • d) ≤
          C * ‖t • d‖ ^ 2
        exact hupper y (t • d)
      have hyx := hfirst y (x - y)
      have hyx' :
          inner ℝ (gradient u y) (x - y) ≤ u x - u y := by
        have hx : y + (x - y) = x := by
          abel
        rw [hx] at hyx
        exact hyx
      have hneg :
          inner ℝ (gradient u x) (y - x) =
            -inner ℝ (gradient u x) (x - y) := by
        rw [show y - x = -(x - y) by abel]
        rw [inner_neg_right]
      rw [hneg] at hmin'
      have h₁ :
          inner ℝ (gradient u x) (t • d) -
              inner ℝ (gradient u y) (t • d) =
            inner ℝ d (t • d) := by
        rw [inner_sub_left]
      have h₂ :
          inner ℝ (gradient u x) (x - y) -
              inner ℝ (gradient u y) (x - y) =
            inner ℝ d (x - y) := by
        rw [inner_sub_left]
      have hgap :
          inner ℝ d (t • d) - C * ‖t • d‖ ^ 2 ≤
            inner ℝ d (x - y) := by
        linarith only [hmin', hu, hyx', h₁, h₂]
      have hself : inner ℝ d d = ‖d‖ ^ 2 :=
        real_inner_self_eq_norm_sq d
      have hdt :
          inner ℝ d (t • d) - C * ‖t • d‖ ^ 2 =
            ‖d‖ ^ 2 / (4 * C) := by
        rw [inner_smul_right, hself, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht]
        dsimp [t]
        field_simp [ne_of_gt hCpos]
        ring
      have hgap' :
          ‖d‖ ^ 2 / (4 * C) ≤ inner ℝ d (x - y) := by
        rw [← hdt]
        exact hgap
      have hmul :
          ‖d‖ ^ 2 ≤ 4 * C * inner ℝ d (x - y) := by
        calc
          ‖d‖ ^ 2 = 4 * C * (‖d‖ ^ 2 / (4 * C)) := by
            field_simp [ne_of_gt hCpos]
          _ ≤ 4 * C * inner ℝ d (x - y) :=
            mul_le_mul_of_nonneg_left hgap' (by linarith)
      exact hmul
    have hnorm (x y : E) :
        ‖gradient u x - gradient u y‖ ≤
          4 * C * ‖x - y‖ := by
      let d : E := gradient u x - gradient u y
      have hco :
          ‖d‖ ^ 2 ≤ 4 * C * inner ℝ d (x - y) := by
        dsimp [d]
        exact hcoercive x y
      have hcs := real_inner_le_norm d (x - y)
      have hmulcs :
          4 * C * inner ℝ d (x - y) ≤
            4 * C * (‖d‖ * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hcs (by linarith)
      have hmul :
          ‖d‖ * (‖d‖ - 4 * C * ‖x - y‖) ≤ 0 := by
        nlinarith [hco, hmulcs]
      by_cases hdzero : ‖d‖ = 0
      · change ‖d‖ ≤ 4 * C * ‖x - y‖
        rw [hdzero]
        positivity
      · have hdpos : 0 < ‖d‖ :=
          lt_of_le_of_ne (norm_nonneg d) (Ne.symm hdzero)
        by_contra hn
        have hnot : 4 * C * ‖x - y‖ < ‖d‖ := lt_of_not_ge hn
        have hprod :
            0 < ‖d‖ * (‖d‖ - 4 * C * ‖x - y‖) :=
          mul_pos hdpos (sub_pos.mpr hnot)
        linarith
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have h4C : 0 ≤ 4 * C := by
      linarith
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal (4 * C) h4C]
    exact hnorm x y
