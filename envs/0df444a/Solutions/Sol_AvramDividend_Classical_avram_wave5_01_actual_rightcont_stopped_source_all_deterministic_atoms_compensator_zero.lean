-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_rightcont_stopped_source_all_deterministic_atoms_compensator_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:44:28.236585+00:00
-- url     : https://prove2.me/submissions/7800510d-a80c-442a-bda8-0eeb13a0d35c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_predictable_occupation_fixed_time_atom_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The literal stopped source jump measure and canonical Levy intensity agree
at every deterministic predictable atom and both give it zero mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ D : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] D →
        μ D = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) D) ∧
      (∀ (t : ℝ≥0) (A : Set Ω),
        MeasurableSet[𝓕.rightCont.predictable] ({t} ×ˢ A) →
        ∀ (B : Set ℝ), MeasurableSet B →
        MT (({t} ×ˢ A) ×ˢ B) =
          (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
           μ.prod (X.ν.restrict (Iio (0 : ℝ))))
            (({t} ×ˢ A) ×ˢ B) ∧
        MT (({t} ×ˢ A) ×ˢ B) = 0) := by
  obtain ⟨Y, hYX, _hc, _hσ, _hν⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hKY : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ Y.X u ω -
            Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, Y.X u ω -
            Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u))) := by
    intro ω
    simpa only [hYX] using hK ω
  obtain ⟨μ, hfin, hagree, _⟩ :=
    avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability X T
  letI : IsProbabilityMeasure P := X.isProbability
  letI : SigmaFinite X.ν :=
    avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields X
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) := inferInstance
  letI : IsFiniteMeasure μ := ⟨hfin⟩
  refine ⟨μ, hfin, hagree, ?_⟩
  have htime (t : ℝ≥0) :
      (((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal) ({t}) = 0 := by
    rw [Measure.map_apply measurable_real_toNNReal
      (measurableSet_singleton t)]
    rw [Measure.restrict_apply
      (measurable_real_toNNReal (measurableSet_singleton t))]
    have hsub :
        (Real.toNNReal ⁻¹' {t}) ∩
          Icc 0 (T : ℝ) ⊆ {(t : ℝ)} := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := hx.2.1
      have hval : (x.toNNReal : ℝ) = x :=
        Real.coe_toNNReal x hx0
      have hz : x.toNNReal = t := hx.1
      exact Set.mem_singleton_iff.mpr (by
        calc
          x = (x.toNNReal : ℝ) := hval.symm
          _ = (t : ℝ) :=
            congrArg (fun y : ℝ≥0 => (y : ℝ)) hz)
    exact le_antisymm
      ((measure_mono hsub).trans (by simp))
      bot_le
  intro t A hPred B hB
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hMzero :
      M (({t} ×ˢ A) ×ˢ B) = 0 :=
    avram_wave5_01_actual_source_predictable_occupation_fixed_time_atom_zero_ae
      Y K hKY M hM t A hPred B hB
  have hC : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (({t} ×ˢ A) ×ˢ B) := hPred.prod hB
  have hMTzero : MT (({t} ×ˢ A) ×ˢ B) = 0 := by
    rw [hMT, Measure.restrict_apply hC]
    apply le_antisymm
    · exact (measure_mono Set.inter_subset_left).trans hMzero.le
    · exact bot_le
  have hμzero : μ ({t} ×ˢ A) = 0 := by
    rw [hagree _ hPred, Measure.prod_prod, htime, zero_mul]
  have hNzero :
      (μ.prod (X.ν.restrict (Iio (0 : ℝ))))
        (({t} ×ˢ A) ×ˢ B) = 0 := by
    rw [Measure.prod_prod, hμzero, zero_mul]
  exact ⟨hMTzero.trans hNzero.symm, hMTzero⟩
