-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb31_original_finite_mark_floor_and_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:39:47.333446+00:00
-- url     : https://prove2.me/submissions/57f07a70-6fb9-484b-b250-031a3f662fb4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb32_finite_cap_closed_interval_compact
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_predictable_left_reserve_jointly_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_K_local_proxy_measurable_of_cap_continuity
import Theorems.Thm_AvramDividend_Classical_avram_bva21_original_uniform_floor_step_measurable
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_m17_closedcap_real_horizon_masked_rate_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w :
    ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (T : ℝ) (hT : 0 <
    T) (u : ℕ → ℕ → ℝ≥0) (hgrid : ∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) (huniform : ∀ n i, (u n i : ℝ) = T * (i
    : ℝ) / ((n : ℝ) + 2)) (hFinite : C ≠ ⊤) (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) (hMassPos : 0 < X.ν (Iio (0 : ℝ))) (hKernel : ∀ s : Set ℝ, IsCompact s → s ⊆ {b : ℝ | 0 ≤ b ∧
    ENNReal.ofReal b ≤ C} → UniformContinuousOn (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) s) (ω : Ω) (hRuinNonzero : ruinTime X x D ω ≠ 0) (hSource : ∀ r : ℝ≥0, r ≤ (⟨T,
    le_of_lt hT⟩ : ℝ≥0) → X.X r ω = (r : ℝ) * X.drift) :
    let U : ℝ≥0 → ℝ := fun t =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    let rate : ℝ≥0 → ℝ := fun t =>
      Real.exp (-(q * (t : ℝ))) * ψ (U t)
    let μ : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal
    let F : ℕ → ℝ → ℝ := fun n r =>
      if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
        let i : ℕ := ⌊(r / T) * ((n : ℝ) + 2)⌋₊
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
           0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
        then rate (u n i) else 0
      else 0
    let G : ℕ → ℝ → ℝ := fun n r =>
      let t : ℝ≥0 := Real.toNNReal r
      if 0 < r ∧ r < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then rate t else 0
    let μreal : Measure ℝ := (volume : Measure ℝ).restrict (Icc 0 T)
    (∀ n, AEStronglyMeasurable (F n) μreal) ∧
    (∀ n, AEStronglyMeasurable (G n) μreal) ∧
    (∀ n, AEStronglyMeasurable
      (fun t : ℝ≥0 =>
        if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
           (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
           0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
        then rate t else 0) μ) := by
  intro U ψ rate μ F G μreal
  have hUGlobal : Measurable U := by
    have hj :=
      avram_integration_sweep9_original_controlled_prestate_ambient_measurable
        X x D hD.1.1
    have hc := hj.comp (measurable_id.prodMk
      (measurable_const : Measurable (fun _ : ℝ≥0 => ω)))
    change Measurable U at hc
    exact hc
  have hψ : ContinuousOn ψ
      {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} :=
    (hKernel _ (avram_bvb32_finite_cap_closed_interval_compact C hFinite)
      Set.Subset.rfl).continuousOn
  have hJ (n : ℕ) : Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then rate t else 0) := by
    simpa only [rate] using
      avram_bvb_m17_closedcap_real_horizon_masked_rate_measurable
        C (ruinTime X x D ω) q T (T - T / ((n : ℝ) + 2))
        U hUGlobal ψ hψ
  let J : ℕ → ℝ≥0 → ℝ := fun n t =>
    if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
        (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
    then rate t else 0
  have hF (n : ℕ) : Measurable (F n) := by
    let c : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
      then rate (u n i) else 0
    change Measurable (fun r : ℝ =>
      if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(r / T) * ((n : ℝ) + 2)⌋₊ else 0)
    exact avram_bva21_original_uniform_floor_step_measurable T hT n c
  have hG (n : ℕ) :
      (G n) = (fun r : ℝ => J n (Real.toNNReal r)) := by
    funext r
    by_cases hpos : 0 < r
    · have hc : ((Real.toNNReal r : ℝ≥0) : ℝ) = r :=
        Real.coe_toNNReal _ (le_of_lt hpos)
      have ht : 0 < Real.toNNReal r := Real.toNNReal_pos.mpr hpos
      simp only [G, J, hc, hpos, ht, true_and]
    · have ht : ¬ 0 < Real.toNNReal r := by
        simpa only [Real.toNNReal_pos] using hpos
      simp [G, J, hpos, ht]
  refine ⟨(fun n => (hF n).aestronglyMeasurable), ?_, ?_⟩
  · intro n
    rw [hG n]
    exact ((hJ n).comp (Measurable.real_toNNReal measurable_id)).aestronglyMeasurable
  · intro (n : ℝ)
    exact (avram_bvb_m17_closedcap_real_horizon_masked_rate_measurable
      C (ruinTime X x D ω) q T (T - T / (n + 2))
      U hUGlobal ψ hψ).aestronglyMeasurable
