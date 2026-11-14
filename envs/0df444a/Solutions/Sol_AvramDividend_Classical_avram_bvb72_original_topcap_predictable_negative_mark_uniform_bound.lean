-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb72_original_topcap_predictable_negative_mark_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:43:58.513069+00:00
-- url     : https://prove2.me/submissions/cac69c17-b8ca-4050-9f07-da7cc1ece9f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bvb72_two_finite_source_measures_uniform_kernel_iterated_compensator_norm_le
import Theorems.Thm_AvramDividend_Classical_avram_bvb73_actual_source_uniform_positive_time_pushforward_finite_mass
import Theorems.Thm_AvramDividend_Classical_avram_bvb75_original_physical_nonnegative_horizon_real_time_measure_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCapTop : C = ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω =>
      ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    let V : ℕ → Ω → ℝ := fun n ω =>
      ∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P,
        ‖V n ω‖ ≤ K * ((X.ν (Iio (0 : ℝ))).toReal * T) := by
  intro δ U H NX J V
  obtain ⟨K, hK, hReward⟩ :=
    avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
      X hBV q hq w hw_cont hw_neg x D hD.1.1 (Real.toNNReal T)
  refine ⟨K, hK, ?_⟩
  intro n
  filter_upwards [hReward] with ω hRewardω
  let μTime : Measure ℝ≥0 :=
    (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
  have hμ : μTime Set.univ < ⊤ := by
    simpa only [μTime] using
      avram_bvb73_actual_source_uniform_positive_time_pushforward_finite_mass T hT
  have hMass : μTime.real Set.univ = T := by
    simpa only [μTime] using
      avram_bvb75_original_physical_nonnegative_horizon_real_time_measure_mass T hT.le
  have hδ : 0 ≤ δ n := div_nonneg hT.le (by positivity)
  have hKernel : ∀ t ∈ Set.univ, ∀ z ∈ Iio (0 : ℝ),
      |H n ((t, ω), z)| ≤ K := by
    intro t ht z hz
    by_cases hmask :
        0 < t ∧ (t : ℝ) < T - δ n ∧
        (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        0 ≤ U t ω ∧ ENNReal.ofReal (U t ω) ≤ C ∧ z < 0
    · have hmaskCopy := hmask
      rcases hmask with ⟨ht0, htcut, hRuin, hU, hCap, hz0⟩
      have htR : (t : ℝ) ≤ (Real.toNNReal T : ℝ) := by
        calc
          (t : ℝ) ≤ T := le_of_lt (lt_of_lt_of_le htcut (sub_le_self T hδ))
          _ = (Real.toNNReal T : ℝ) := (Real.coe_toNNReal T hT.le).symm
      have htNN : t ≤ Real.toNNReal T := by exact_mod_cast htR
      have hPoint := hRewardω t htNN hU z hz0
      simpa only [H, U, if_pos hmaskCopy] using hPoint
    · simp only [H, if_neg hmask, abs_zero]
      exact hK
  have hBound :=
    avram_bvb72_two_finite_source_measures_uniform_kernel_iterated_compensator_norm_le
      μTime Set.univ (by measurability) hμ
      X.ν (Iio (0 : ℝ)) measurableSet_Iio hActivity
      (fun t z => H n ((t, ω), z)) K hK hKernel
  have hBoundNew := hBound
  change ‖∫ t in Set.univ, ∫ z in Iio (0 : ℝ),
      H n ((t, ω), z) ∂X.ν ∂μTime‖ ≤
      (K * (X.ν (Iio (0 : ℝ))).toReal) * μTime.real Set.univ at hBoundNew
  rw [hMass] at hBoundNew
  have hV : ‖V n ω‖ ≤ (K * (X.ν (Iio (0 : ℝ))).toReal) * T := by
    simpa only [V, μTime, setIntegral_univ] using hBoundNew
  simpa only [mul_assoc] using hV
