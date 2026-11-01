-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_law_from_fine_original_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T23:01:48.909209+00:00
-- url     : https://prove2.me/submissions/70e748d7-2fdc-4672-b91e-3e13d1577e12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_count_level_ae_eq_measurable_liminf_grid_deficit
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_jump_count_eq_drift_deficit_count_for_all_fine_partitions_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_original_grid_drift_deficit_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_grid_active_poisson_scaling_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (ht : ∀ n : ℕ, Monotone (grid n))
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (h : ℕ → ℝ)
    (hgap : ∀ n i : ℕ, i < n →
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)) = h n)
    (r : ℝ)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) *
      (1 - Real.exp (-(h n * (X.ν (Iio (0 : ℝ))).toReal))))
      atTop (𝓝 r))
    (k : ℕ) :
    P.real {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (k : ENNReal)} =
      Real.exp (-r) * r ^ k / (k.factorial : ℝ) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let A : ℕ → Set Ω := fun n =>
    {ω : Ω |
      ((Finset.range n).filter (fun i =>
        X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
          X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card = k}
  let E : Set Ω := Filter.liminf A atTop
  let B : Set Ω := {ω : Ω | ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (k : ENNReal)}
  have hProxy :=
    avram_wave4_04a_bv_actual_intrinsic_count_level_ae_eq_measurable_liminf_grid_deficit
      X hBV hFinite T hT grid hGrid hMesh k
  have hBeqE : ∀ᵐ ω ∂P, ω ∈ B ↔ ω ∈ E := hProxy.2
  have hMeasA (n : ℕ) : MeasurableSet (A n) :=
    (avram_wave4_04a_actual_original_grid_drift_deficit_count_measurable
      X n (grid n)) (measurableSet_singleton k)
  have hSource :=
    avram_wave4_04a_bv_actual_jump_count_eq_drift_deficit_count_for_all_fine_partitions_ae
      X hBV hFinite T hT
  have hConvergesEvents :
      ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ω ∈ A n ↔ ω ∈ E := by
    filter_upwards [hSource, hBeqE] with ω hSourceω hBeqEω
    obtain ⟨δ, hδ, hfine⟩ := hSourceω
    have hPos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_gt_atTop 0
    have hSmall := hMesh δ hδ
    filter_upwards [hPos, hSmall] with n hn hwidth
    obtain ⟨hStrict, hZero, hEnd⟩ := hGrid n hn
    have hExact := hfine n (grid n) hStrict hZero hEnd hwidth
    have hSet :
        {i : ℕ | i < n ∧
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ))} =
        (↑((Finset.range n).filter (fun i =>
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))) :
          Set ℕ) := by
      ext i
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range]
    rw [hSet] at hExact
    have hCount : ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (((Finset.range n).filter (fun i =>
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card : ENNReal) := by
      simpa only [Set.ncard_coe_finset] using hExact
    constructor
    · intro hAn
      have hCard : ((Finset.range n).filter (fun i =>
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card = k := hAn
      have hK : ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (k : ENNReal) :=
        hCount.trans (by exact_mod_cast hCard)
      exact hBeqEω.mp hK
    · intro hEn
      have hK : ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (k : ENNReal) := hBeqEω.mpr hEn
      have hCast : (((Finset.range n).filter (fun i =>
          X.X (grid n (i + 1)) ω - X.X (grid n i) ω <
            X.drift * (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)))).card : ENNReal) = (k : ENNReal) :=
        hCount.symm.trans hK
      exact_mod_cast hCast
  have hMass : Tendsto (fun n : ℕ => P (A n)) atTop (𝓝 (P E)) :=
    MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      (L := atTop) hProxy.1 hMeasA hConvergesEvents
  have hRealMass : Tendsto (fun n : ℕ => P.real (A n))
      atTop (𝓝 (P.real E)) := by
    have hReal :=
      (ENNReal.tendsto_toReal (measure_ne_top P E)).comp hMass
    change Tendsto (fun n : ℕ => P.real (A n))
      atTop (𝓝 (P.real E)) at hReal
    exact hReal
  have hGridPoisson :=
    avram_wave4_04a_bv_actual_grid_active_poisson_scaling_limit
      X hBV hFinite grid ht h hgap r hr k
  have hGridPoisson' : Tendsto (fun n : ℕ => P.real (A n))
      atTop (𝓝 (Real.exp (-r) * r ^ k / (k.factorial : ℝ))) := by
    simpa only [A] using hGridPoisson
  have hPoisson : P.real E =
      Real.exp (-r) * r ^ k / (k.factorial : ℝ) :=
    tendsto_nhds_unique hRealMass hGridPoisson'
  have hEventEq : B =ᵐ[P] E := by
    filter_upwards [hBeqE] with ω hω
    exact propext hω
  have hCountMeasure : P B = P E := MeasureTheory.measure_congr hEventEq
  change P.real B = Real.exp (-r) * r ^ k / (k.factorial : ℝ)
  calc
    P.real B = P.real E := congrArg ENNReal.toReal hCountMeasure
    _ = _ := hPoisson
