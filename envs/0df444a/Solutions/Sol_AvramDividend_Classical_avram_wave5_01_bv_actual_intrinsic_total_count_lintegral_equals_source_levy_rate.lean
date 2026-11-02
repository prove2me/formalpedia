-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_bv_actual_intrinsic_total_count_lintegral_equals_source_levy_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:20:46.666375+00:00
-- url     : https://prove2.me/submissions/8b7752fb-09d0-4c3c-bfd2-b55f78ac70da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_source_count_nat_supported_summable_poisson_moment
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact ENNReal expected intrinsic source count, preserving every
original path, its own filtration and its actual Levy triplet. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let J : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ))
  obtain ⟨F, hFm, hFae, hN, hSumm, hReal⟩ :=
    avram_wave5_01_bv_actual_source_count_nat_supported_summable_poisson_moment
      X hBV hFinite T hT grid hGrid hMesh hBound
  have hFmeas : Measurable F := hFm.mono (𝓕.le T) le_rfl
  have hPoint : ∀ᵐ ω ∂P,
      F ω = ∑' k : ℕ,
        if F ω = (k : ℝ≥0∞) then (k : ℝ≥0∞) else 0 := by
    filter_upwards [hN] with ω ⟨k, hk⟩
    rw [hk]
    calc
      (k : ℝ≥0∞) = ∑' j : ℕ,
          if j = k then (j : ℝ≥0∞) else 0 :=
        (tsum_ite_eq k (fun j : ℕ => (j : ℝ≥0∞))).symm
      _ = ∑' j : ℕ,
          if (k : ℝ≥0∞) = (j : ℝ≥0∞) then (j : ℝ≥0∞) else 0 := by
        apply tsum_congr
        intro j
        simp only [Nat.cast_inj, eq_comm]
  have hSets (k : ℕ) :
      MeasurableSet {ω : Ω | F ω = (k : ℝ≥0∞)} :=
    hFmeas (measurableSet_singleton (k : ℝ≥0∞))
  have hAEm (k : ℕ) :
      AEMeasurable
        (fun ω : Ω => if F ω = (k : ℝ≥0∞)
          then (k : ℝ≥0∞) else 0) P :=
    (Measurable.ite (hSets k) measurable_const measurable_const).aemeasurable
  have hInd (k : ℕ) :
      (∫⁻ ω, (if F ω = (k : ℝ≥0∞)
        then (k : ℝ≥0∞) else 0) ∂P) =
      (k : ℝ≥0∞) * P {ω : Ω | F ω = (k : ℝ≥0∞)} := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      (lintegral_indicator_const (hSets k) (k : ℝ≥0∞))
  have hTerm (k : ℕ) :
      ENNReal.ofReal ((k : ℝ) *
        P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) =
      (k : ℝ≥0∞) * P {ω : Ω | F ω = (k : ℝ≥0∞)} := by
    have hfinite :
        P {ω : Ω | F ω = (k : ℝ≥0∞)} ≠ ⊤ :=
      (measure_lt_top P _).ne
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg k)]
    simpa only [Measure.real, ENNReal.ofReal_natCast,
      ENNReal.ofReal_toReal hfinite]
  have hPositive (k : ℕ) :
      0 ≤ (k : ℝ) *
        P.real {ω : Ω | F ω = (k : ℝ≥0∞)} :=
    mul_nonneg (Nat.cast_nonneg k) ENNReal.toReal_nonneg
  have hMeanF :
      (∫⁻ ω, F ω ∂P) =
        ENNReal.ofReal ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal) := by
    calc
      _ = ∫⁻ ω, ∑' k : ℕ,
          if F ω = (k : ℝ≥0∞) then (k : ℝ≥0∞) else 0 ∂P :=
        lintegral_congr_ae hPoint
      _ = ∑' k : ℕ, ∫⁻ ω,
          (if F ω = (k : ℝ≥0∞) then (k : ℝ≥0∞) else 0) ∂P :=
        lintegral_tsum hAEm
      _ = ∑' k : ℕ, (k : ℝ≥0∞) *
          P {ω : Ω | F ω = (k : ℝ≥0∞)} :=
        tsum_congr hInd
      _ = ∑' k : ℕ,
          ENNReal.ofReal ((k : ℝ) *
            P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) := by
        apply tsum_congr
        intro k
        exact (hTerm k).symm
      _ = ENNReal.ofReal (∑' k : ℕ, (k : ℝ) *
          P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) :=
        (ENNReal.ofReal_tsum_of_nonneg hPositive hSumm).symm
      _ = _ := by rw [hReal]
  have hRate :
      ENNReal.ofReal ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg T),
      ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_toReal (ne_of_lt hFinite)]
  change (∫⁻ ω, J ω ∂P) =
    (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))
  calc
    _ = ∫⁻ ω, F ω ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hFae] with ω hω
      exact hω.symm
    _ = _ := hMeanF.trans hRate
