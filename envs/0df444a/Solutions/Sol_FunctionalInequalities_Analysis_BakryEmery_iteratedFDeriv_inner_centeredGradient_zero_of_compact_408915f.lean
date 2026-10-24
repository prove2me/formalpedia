-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_of_compact_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:47:47.15238+00:00
-- url     : https://prove2.me/submissions/dfe3246a-902d-4689-8c31-d7d2c7c67312

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_directional_centeredGradient_logLaplace_zero_of_compact_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_directional_bilinear_408915f

section
noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- The directional list convention is exactly the raw iterated Fréchet derivative. -/
theorem FunctionalInequalities.Analysis.directional_ofFn {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) f x = iteratedFDeriv ℝ m f x h := by
  induction m generalizing x with
  | zero => simp [directional]
  | succ m IH =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directional (List.ofFn (Fin.tail h)) f) x (h 0) = _
    have he : directional (List.ofFn (Fin.tail h)) f =
        fun y => iteratedFDeriv ℝ m f y (Fin.tail h) := funext (fun y => IH (Fin.tail h) y)
    rw [he]
    exact ((hf.differentiable_iteratedFDeriv (m := m)
      (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)) x).iteratedFDeriv_succ_apply_left').symm
end
end
end
end

section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section CompactSupport
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
/-- A law with compact support has every exponential moment. -/
theorem FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp (μ : Measure F) [IsFiniteMeasure μ]
    (hc : IsCompact μ.support) (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖)) μ := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : F)
  refine (integrable_const (Real.exp (|r| * max R 0))).mono' (by fun_prop) ?_
  filter_upwards [μ.support_mem_ae] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    r * ‖x‖ ≤ |r| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |r| * max R 0 := by
      gcongr
      exact (by simpa using hR hx : ‖x‖ ≤ R).trans (le_max_left _ _)
end CompactSupport
end
end
end
end

section
noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
/-- Exact raw iterated Fréchet Leibniz expansion, retaining every subset allocation. -/
theorem FunctionalInequalities.Analysis.iteratedFDeriv_bilinear (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : ℕ) (h : Fin m → E) (x : E) :
    iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x h =
      ∑ q : Fin m → Bool,
        B (directional (selected h q) f x)
          (directional (selected h (fun i => !(q i))) g x) := by
  have hB : ContDiff ℝ ∞ (fun y => B (f y) (g y)) := by
    simpa only [Function.comp_def] using B.isBoundedBilinearMap.contDiff.comp (hf.prodMk hg)
  rw [← directional_ofFn hB]
  exact directional_bilinear_408915f B hf hg m h x
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The mask selector returns the empty list exactly for the all-`false` mask. -/
theorem FunctionalInequalities.Analysis.selected_eq_nil_iff {m : ℕ} (h : Fin m → E) (q : Fin m → Bool) :
    selected h q = [] ↔ ∀ i, q i = false := by
    induction m with
    | zero =>
        simp [selected]
    | succ m ih =>
        cases hq0 : q 0 with
        | false =>
            simp [selected, hq0, ih (Fin.tail h) (Fin.tail q),
              Fin.forall_fin_succ, Fin.tail]
        | true =>
            simp [selected, hq0, Fin.forall_fin_succ]
end
end
end
end

section
noncomputable section
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
/-- Leibniz rule for `⟪f, M g⟫`: `Dᵐ⟪f, M g⟫(x)[h] = Σ_q ⟪∂_{h_q} f(x), M ∂_{h_{¬q}} g(x)⟫`. -/
theorem FunctionalInequalities.Analysis.iteratedFDeriv_inner_clm {f g : D → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (M : E →L[ℝ] E) (m : ℕ) (h : Fin m → D) (x : D) :
    iteratedFDeriv ℝ m (fun y => ⟪f y, M (g y)⟫) x h =
      ∑ q : Fin m → Bool,
        ⟪directional (selected h q) f x, M (directional (selected h (fun i => !(q i))) g x)⟫ := by
    let B : E →L[ℝ] E →L[ℝ] ℝ :=
      (ContinuousLinearMap.compL ℝ E E ℝ).flip M ∘L
        (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
    have hB : ∀ a b : E, B a b = ⟪a, M b⟫ := fun a b => by
      change (⟪a, M b⟫ : ℝ) = ⟪a, M b⟫
      rfl
    have hfun : (fun y => B (f y) (g y)) = fun y => ⟪f y, M (g y)⟫ :=
      funext fun y => hB _ _
    rw [← hfun, iteratedFDeriv_bilinear B hf hg m h x]
    exact Finset.sum_congr rfl fun q _ => hB _ _
end
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Raw (74) expansion**: `Dᵐ⟪v, M v⟫(0)[h] = Σ_{∅ ≠ q ≠ [m]} ⟪κ_{|q|+1}(h_q,·), M κ_{m−|q|+1}(h_{¬q},·)⟫`. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (M : E →L[ℝ] E) (m : ℕ) (h : Fin m → E) :
    iteratedFDeriv ℝ m (fun z : E =>
        ⟪gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) z - gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) 0,
          M (gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) z - gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) 0)⟫) 0 h =
      ∑ q ∈ (Finset.univ.filter fun q : Fin m → Bool => (∃ i, q i = true) ∧ (∃ i, q i = false)),
        ⟪FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) (FunctionalInequalities.Analysis.selected h q),
          M (FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) (FunctionalInequalities.Analysis.selected h (fun i => !(q i))))⟫ := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    have hΛ : ContDiff ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) :=
      FunctionalInequalities.Analysis.BakryEmery.contDiff_logLaplace _ (FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp _ hc)
    have hg : ContDiff ℝ ∞ (gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E))) := by
      change
        ContDiff ℝ ∞
          ((InnerProductSpace.toDual ℝ E).symm ∘
            fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)))
      exact
        (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp
          (hΛ.fderiv_right (by simp))
    have hv : ContDiff ℝ ∞ (fun z : E =>
        gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) z -
          gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) 0) :=
      hg.sub contDiff_const
    rw [FunctionalInequalities.Analysis.iteratedFDeriv_inner_clm hv hv M m h 0]
    simp_rw [FunctionalInequalities.Analysis.BakryEmery.directional_centeredGradient_logLaplace_zero_of_compact_408915f μ hc]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun q : Fin m → Bool => (∃ i, q i = true) ∧ (∃ i, q i = false))]
    have hzero :
        (Finset.univ.filter
          (fun q : Fin m → Bool =>
            ¬((∃ i, q i = true) ∧ (∃ i, q i = false)))).sum
          (fun q =>
            ⟪if FunctionalInequalities.Analysis.selected h q = [] then 0
                else FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) (FunctionalInequalities.Analysis.selected h q),
              M (if FunctionalInequalities.Analysis.selected h (fun i => !(q i)) = [] then 0
                else FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E)
                  (FunctionalInequalities.Analysis.selected h (fun i => !(q i))))⟫) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hn := (Finset.mem_filter.mp hq).2
      have hor : (∀ i, q i = false) ∨ (∀ i, q i = true) := by
        by_cases hf : ∀ i, q i = false
        · exact Or.inl hf
        · right
          obtain ⟨i, hi⟩ : ∃ i, q i ≠ false := not_forall.mp hf
          have ht : q i = true := by
            cases hqi : q i with
            | false => exact False.elim (hi hqi)
            | true => rfl
          have hnf : ¬∃ i, q i = false := by
            intro hfalse
            exact hn ⟨⟨i, ht⟩, hfalse⟩
          intro j
          cases hqj : q j with
          | false => exact False.elim (hnf ⟨j, hqj⟩)
          | true => rfl
      rcases hor with hf | ht
      · have hs : FunctionalInequalities.Analysis.selected h q = [] :=
          (FunctionalInequalities.Analysis.selected_eq_nil_iff h q).2 hf
        rw [hs]
        simp
      · have hs : FunctionalInequalities.Analysis.selected h (fun i => !(q i)) = [] :=
          (FunctionalInequalities.Analysis.selected_eq_nil_iff h (fun i => !(q i))).2 (by
            intro i
            simp [ht i])
        rw [hs]
        simp
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro q hq
    have hmem := (Finset.mem_filter.mp hq).2
    have hqne : FunctionalInequalities.Analysis.selected h q ≠ [] := by
      intro hs
      have hall := (FunctionalInequalities.Analysis.selected_eq_nil_iff h q).1 hs
      obtain ⟨i, hi⟩ := hmem.1
      have hfalse := hall i
      rw [hi] at hfalse
      cases hfalse
    have hqne' : FunctionalInequalities.Analysis.selected h (fun i => !(q i)) ≠ [] := by
      intro hs
      have hall :=
        (FunctionalInequalities.Analysis.selected_eq_nil_iff h (fun i => !(q i))).1 hs
      obtain ⟨i, hi⟩ := hmem.2
      have hfalse := hall i
      simp [hi] at hfalse
    simp [hqne, hqne']
