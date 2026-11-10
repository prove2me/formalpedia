-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess18_original_stopped_zero_contact_finite_grid_L1_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T19:44:51.12234+00:00
-- url     : https://prove2.me/submissions/81308a20-79f8-454e-aa3e-ff387677b3e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess17_original_zero_prestate_source_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_finite_grid_eventwise_centering

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (r : ι → ℕ → ℝ≥0)
    (hsr : ∀ i n, s i < r i n) (hrt : ∀ i n, r i n ≤ t i)
    (hShort : ∀ i, Tendsto (fun n => r i n - s i) atTop (𝓝 0))
    (hLong : ∀ i, Tendsto (fun n => t i - r i n) atTop (𝓝 (t i - s i)))
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (v : ι → ℝ) :
    let J : ι → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)))
       (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ))
    let M : Ω → ℝ := fun ω => ∑ i : ι,
      (if (s i : ℝ≥0∞) < ruinTime X x D ω ∧
          Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i) = 0
        then v i else 0) *
      ((J i ω).toReal -
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal)
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
  classical
  let H : ι → Ω → ℝ := fun i ω =>
    if (s i : ℝ≥0∞) < ruinTime X x D ω ∧
        Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i) = 0
      then v i else 0
  let J : ι → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0}).map
     (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)))
     (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ))
  have hStop := ruinTime_stopping_rightCont_filtration X x D hD
  have hMeas (i : ι) :
      StronglyMeasurable[𝓕.rightCont (s i)] (H i) := by
    let A : Set Ω := {ω | (s i : ℝ≥0∞) < ruinTime X x D ω ∧
      Function.leftLim
        (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i) = 0}
    have hz :=
      avram_bv_excess17_original_zero_prestate_source_measurable
        X x D hD (s i)
    have ht : MeasurableSet[𝓕.rightCont (s i)]
        {ω : Ω | (s i : ℝ≥0∞) < ruinTime X x D ω} := by
      have hle := hStop (s i)
      have heq : {ω : Ω | (s i : ℝ≥0∞) < ruinTime X x D ω} =
          {ω : Ω | ¬ ruinTime X x D ω ≤ (s i : ℝ≥0∞)} := by
        ext ω
        simp [not_le]
      rw [heq]
      exact hle.compl
    have hA : MeasurableSet[𝓕.rightCont (s i)] A := ht.inter hz
    simpa only [H, A, Set.mem_setOf_eq] using
      (measurable_const.ite hA measurable_const).stronglyMeasurable
  have hHAE (i : ι) : AEStronglyMeasurable (H i) P :=
    ((hMeas i).mono (𝓕.rightCont.le (s i))).aestronglyMeasurable
  have hb (i : ι) : ∀ᵐ ω ∂P, ‖H i ω‖ ≤ ‖v i‖ := by
    filter_upwards [] with ω
    dsimp [H]
    split_ifs <;> simp
  have hJ (i : ι) (ω : Ω) : J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)))
       (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) := rfl
  have hCell (i : ι) : Integrable
      (fun ω => H i ω * ((J i ω).toReal -
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal)) P :=
    (avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
      X (s i) (t i) (hst i) (r i) (hsr i) (hrt i)
      (hShort i) (hLong i) (Iio (0 : ℝ)) measurableSet_Iio hFinite
      (J i) (hJ i) (H i) ‖v i‖ (hMeas i) (hHAE i) (hb i)).1
  have hAll : Integrable (fun ω => ∑ i : ι,
      H i ω * ((J i ω).toReal -
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal)) P :=
    integrable_finset_sum Finset.univ (fun i _ => hCell i)
  have hMean :=
    avram_ubv_jump12_original_finite_grid_eventwise_centering
      X s t hst r hsr hrt hShort hLong
      (fun _ => Iio (0 : ℝ)) (fun _ => measurableSet_Iio)
      (fun _ => hFinite) J hJ H (fun i => ‖v i‖)
      hMeas hHAE hb Set.univ (fun _ => MeasurableSet.univ)
  dsimp only
  constructor
  · simpa only [H, J] using hAll
  · simpa only [H, J, Measure.restrict_univ] using hMean
