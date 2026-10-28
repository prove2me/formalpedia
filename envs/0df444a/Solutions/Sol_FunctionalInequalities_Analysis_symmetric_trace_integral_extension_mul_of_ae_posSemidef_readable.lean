-- Prove2me | solution 1 for FunctionalInequalities.Analysis.symmetric_trace_integral_extension_mul_of_ae_posSemidef_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:51.743769+00:00
-- url     : https://prove2.me/submissions/b6f9875e-2e01-4fbb-8931-a426ea166119

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Integral
import Theorems.Thm_FunctionalInequalities_Analysis_jordan_trace_domination_readable
import Theorems.Thm_FunctionalInequalities_Analysis_symmetric_jordan_decomposition_readable
import Theorems.Thm_FunctionalInequalities_Analysis_trace_energy_nonneg_readable

noncomputable section
open Matrix MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Arbitrary real coefficient, almost-everywhere positive semidefinite field: if every positive semidefinite `A`
has `x ↦ tr(A H(x) A H(x))` integrable with `∫ tr(A H A H) dν ≤ C tr(A²)`, then every symmetric `B` has the same.
No sign condition on `C`; arbitrary measure and finite index type (empty allowed). -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {C : ℝ}
    (H : Ω → Matrix ι ι ℝ)
    (hH_meas : ∀ i j, Measurable (fun x => H x i j))
    (hH_psd : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hPSD : ∀ A : Matrix ι ι ℝ, A.PosSemidef →
      Integrable (fun x => (A * H x * A * H x).trace) ν ∧
        (∫ x, (A * H x * A * H x).trace ∂ν) ≤
          C * (A * A).trace)
    {B : Matrix ι ι ℝ} (hB : B.IsSymm) :
    Integrable (fun x => (B * H x * B * H x).trace) ν ∧
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        C * (B * B).trace := by
  obtain ⟨P, N, hP, hN, hdec, hPN, hNP, htrace⟩ :=
    FunctionalInequalities.Analysis.symmetric_jordan_decomposition_readable B hB
  obtain ⟨hP_int, hP_bound⟩ := hPSD P hP
  obtain ⟨hN_int, hN_bound⟩ := hPSD N hN
  have hmeas (A : Matrix ι ι ℝ) :
      Measurable (fun x => (A * H x * A * H x).trace) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Finset.measurable_sum _ (fun j _ => ?_)
    refine Measurable.mul ?_ (hH_meas j i)
    refine Finset.measurable_sum _ (fun k _ => ?_)
    refine Measurable.mul ?_ measurable_const
    refine Finset.measurable_sum _ (fun l _ => ?_)
    exact measurable_const.mul (hH_meas l k)
  have hP_nonneg : ∀ᵐ x ∂ν,
      0 ≤ (P * H x * P * H x).trace := by
    filter_upwards [hH_psd] with x hx
    exact FunctionalInequalities.Analysis.trace_energy_nonneg_readable (Matrix.isHermitian_iff_isSymm.mp (Matrix.PosSemidef.isHermitian hP)) hx
  have hN_nonneg : ∀ᵐ x ∂ν,
      0 ≤ (N * H x * N * H x).trace := by
    filter_upwards [hH_psd] with x hx
    exact FunctionalInequalities.Analysis.trace_energy_nonneg_readable (Matrix.isHermitian_iff_isSymm.mp (Matrix.PosSemidef.isHermitian hN)) hx
  have hB_nonneg : ∀ᵐ x ∂ν,
      0 ≤ (B * H x * B * H x).trace := by
    filter_upwards [hH_psd] with x hx
    exact FunctionalInequalities.Analysis.trace_energy_nonneg_readable hB hx
  have hdom : ∀ᵐ x ∂ν,
      (B * H x * B * H x).trace ≤
        (P * H x * P * H x).trace + (N * H x * N * H x).trace := by
    filter_upwards [hH_psd] with x hx
    rw [hdec]
    exact FunctionalInequalities.Analysis.jordan_trace_domination_readable hP hN
      (Matrix.isHermitian_iff_isSymm.mp (Matrix.PosSemidef.isHermitian hx))
  have hsum_int :
      Integrable
        (fun x =>
          (P * H x * P * H x).trace + (N * H x * N * H x).trace) ν := by
    exact hP_int.add hN_int
  have hB_int :
      Integrable (fun x => (B * H x * B * H x).trace) ν := by
    refine hsum_int.mono (hmeas B).aestronglyMeasurable ?_
    filter_upwards [hB_nonneg, hP_nonneg, hN_nonneg, hdom] with x hB0 hP0 hN0 hd
    rw [Real.norm_eq_abs, abs_of_nonneg hB0]
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hP0 hN0)]
    exact hd
  have hIntDom :
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        ∫ x, ((P * H x * P * H x).trace +
          (N * H x * N * H x).trace) ∂ν := by
    exact integral_mono_ae hB_int hsum_int hdom
  refine ⟨hB_int, ?_⟩
  calc
    (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        ∫ x, ((P * H x * P * H x).trace +
          (N * H x * N * H x).trace) ∂ν := hIntDom
    _ = (∫ x, (P * H x * P * H x).trace ∂ν) +
        ∫ x, (N * H x * N * H x).trace ∂ν :=
      integral_add hP_int hN_int
    _ ≤ C * (P * P).trace + C * (N * N).trace :=
      add_le_add hP_bound hN_bound
    _ = C * (B * B).trace := by
      calc
        C * (P * P).trace + C * (N * N).trace =
            C * ((P * P).trace + (N * N).trace) := by ring
        _ = C * (B * B).trace := by rw [← htrace]
