-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.directional_centeredGradient_logLaplace_zero_of_compact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:08.290616+00:00
-- url     : https://prove2.me/submissions/6f5bdf81-b896-4e8f-9e92-86455d1a3252

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Leibniz
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact_readable

section
noncomputable section
open scoped ContDiff
section
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

section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
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

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Directional derivatives at `0` of the centred CGF gradient: `0` for the empty list, `κ_{|l|+1}(l, ·)` otherwise. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (l : List E) :
    FunctionalInequalities.Analysis.directional l (fun z : E =>
        gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) z - gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) 0) 0 =
      if l = [] then 0 else FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) l := by
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
    split_ifs with hl
    · subst hl
      change _ - _ = 0
      exact sub_self _
    · have h1 := FunctionalInequalities.Analysis.directional_ofFn hv l.length l.get 0
      rw [List.ofFn_get] at h1
      rw [h1,
        FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact_readable μ hc _
          (List.length_pos_iff.mpr hl) _, List.ofFn_get]
