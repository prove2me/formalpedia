-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.variance_le_mul_energy_of_tendsto_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:41:18.389992+00:00
-- url     : https://prove2.me/submissions/3e55fd20-99e3-453c-8ff3-fdcab2b22599

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_WeakLimit

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]
omit [MeasurableSpace E] in
/-- Source: local Hilbert-geometry helper using Mathlib's `toDual_gradient` and the
norm-preserving Riesz map `InnerProductSpace.toDual`. -/
theorem FunctionalInequalities.Poincare.SmoothTest.norm_fderiv_eq_norm_gradient (f : E → ℝ) (x : E) :
    ‖fderiv ℝ f x‖ = ‖gradient f x‖ := by
  rw [← toDual_gradient]
  exact (InnerProductSpace.toDual ℝ E).norm_map _
/-- Source: local consequence of `norm_fderiv_eq_norm_gradient` and `integral_congr_ae`.
The energy also equals the integral of the squared Fréchet-derivative operator norm. -/
theorem FunctionalInequalities.Poincare.SmoothTest.energy_eq_fderiv (μ : Measure E) (f : E → ℝ) :
    energy μ f = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖gradient f x‖ ^ 2 = ‖fderiv ℝ f x‖ ^ 2
    rw [norm_fderiv_eq_norm_gradient]
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
/-- **Weak passage of the Poincaré inequality on a compactly supported smooth test**: if `μ_j → μ`
weakly, `C_j → C` and `Var_{μ_j} f ≤ C_j ∫‖∇f‖² dμ_j`, then `Var_μ f ≤ C ∫‖∇f‖² dμ`. -/
theorem solution {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hlim : Tendsto μs atTop (𝓝 μ)) {Cseq : ℕ → ℝ} {C : ℝ} (hC : Tendsto Cseq atTop (𝓝 C))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (h : ∀ j, variance f (μs j : Measure E) ≤ Cseq j * FunctionalInequalities.Poincare.SmoothTest.energy (μs j : Measure E) f) :
    variance f (μ : Measure E) ≤ C * FunctionalInequalities.Poincare.SmoothTest.energy (μ : Measure E) f := by
      obtain ⟨Bf, hBf⟩ := hc.exists_bound_of_continuous hf.continuous
      let gf : BoundedContinuousFunction E ℝ :=
        BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous Bf hBf

      have hfc : HasCompactSupport (fun x => f x ^ 2) := by
        apply hc.mono
        intro x hx
        by_contra hfx
        have hzero : f x = 0 := by
          simpa [Function.mem_support] using hfx
        exact hx (by simp [hzero])

      have hfs : Continuous (fun x => f x ^ 2) := by
        convert hf.continuous.pow 2 using 1
        ext x
        rfl

      obtain ⟨Bf2, hBf2⟩ := hfc.exists_bound_of_continuous hfs
      let gf2 : BoundedContinuousFunction E ℝ :=
        BoundedContinuousFunction.ofNormedAddCommGroup
          (fun x => f x ^ 2) hfs Bf2 hBf2

      have hfd : Continuous (fderiv ℝ f) :=
        hf.continuous_fderiv (by simp)

      have hgradc : HasCompactSupport (fun x => ‖fderiv ℝ f x‖ ^ 2) := by
        apply (hc.fderiv ℝ).mono
        intro x hx
        by_contra hdf
        have hzero : fderiv ℝ f x = 0 := by
          simpa [Function.mem_support] using hdf
        exact hx (by simp [hzero])

      have hgrads : Continuous (fun x => ‖fderiv ℝ f x‖ ^ 2) := by
        convert hfd.norm.pow 2 using 1
        ext x
        rfl

      obtain ⟨Bg, hBg⟩ := hgradc.exists_bound_of_continuous hgrads
      let gg : BoundedContinuousFunction E ℝ :=
        BoundedContinuousFunction.ofNormedAddCommGroup
          (fun x => ‖fderiv ℝ f x‖ ^ 2) hgrads Bg hBg

      have hfi :
          Tendsto (fun j => ∫ x, f x ∂(μs j : Measure E))
            atTop (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
        simpa [gf] using
          (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim gf)

      have hf2i :
          Tendsto (fun j => ∫ x, f x ^ 2 ∂(μs j : Measure E))
            atTop (𝓝 (∫ x, f x ^ 2 ∂(μ : Measure E))) := by
        simpa [gf2] using
          (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim gf2)

      have hgi :
          Tendsto (fun j => ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μs j : Measure E))
            atTop (𝓝 (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μ : Measure E))) := by
        simpa [gg] using
          (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim gg)

      have hmem (ν : ProbabilityMeasure E) :
          MemLp f 2 (ν : Measure E) := by
        apply MemLp.of_bound (μ := (ν : Measure E)) (p := (2 : ENNReal))
        · exact gf.continuous.aestronglyMeasurable
        · filter_upwards [] with x
          exact hBf x

      have hvar (ν : ProbabilityMeasure E) :
          variance f (ν : Measure E) =
            (∫ x, f x ^ 2 ∂(ν : Measure E)) -
              (∫ x, f x ∂(ν : Measure E)) ^ 2 := by
        exact variance_eq_sub (hmem ν)

      have hleft :
          Tendsto
            (fun j =>
              (∫ x, f x ^ 2 ∂(μs j : Measure E)) -
                (∫ x, f x ∂(μs j : Measure E)) ^ 2)
            atTop
            (𝓝
              ((∫ x, f x ^ 2 ∂(μ : Measure E)) -
                (∫ x, f x ∂(μ : Measure E)) ^ 2)) := by
        exact hf2i.sub (hfi.pow 2)

      have hright :
          Tendsto
            (fun j =>
              Cseq j * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μs j : Measure E))
            atTop
            (𝓝
              (C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μ : Measure E))) := by
        exact hC.mul hgi

      have h' :
          ∀ j, variance f (μs j : Measure E) ≤
            Cseq j * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μs j : Measure E) := by
        intro j
        rw [← FunctionalInequalities.Poincare.SmoothTest.energy_eq_fderiv]
        exact h j

      have hlimineq :
          (∫ x, f x ^ 2 ∂(μ : Measure E)) -
              (∫ x, f x ∂(μ : Measure E)) ^ 2
            ≤ C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μ : Measure E) := by
        apply le_of_tendsto_of_tendsto' hleft hright
        intro j
        rw [← hvar (μs j)]
        exact h' j

      calc
        variance f (μ : Measure E) =
            (∫ x, f x ^ 2 ∂(μ : Measure E)) -
              (∫ x, f x ∂(μ : Measure E)) ^ 2 := hvar μ
        _ ≤ C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(μ : Measure E) := hlimineq
        _ = C * FunctionalInequalities.Poincare.SmoothTest.energy (μ : Measure E) f := by
          rw [FunctionalInequalities.Poincare.SmoothTest.energy_eq_fderiv]
