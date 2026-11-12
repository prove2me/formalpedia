-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_original_smallband_finsum_card_le_total_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:29:44.882985+00:00
-- url     : https://prove2.me/submissions/2c5ed28c-c76f-47bf-b85c-157dd4c6a782

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18j_public_original_compensated_finsum
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0,
      let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ))
      ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ∃ F : Finset ℝ≥0,
          (∀ u : ℝ≥0, u ∈ F ↔
             0 < u ∧ u ≤ t ∧
             -1 < X.X u ω -
               Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
             X.X u ω -
               Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
               -(1 / ((k : ℝ) + 1))) ∧
          (F.card : ℝ) ≤ (N ω).toReal := by
  intro T
  classical
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ))
  have hNfinite : ∀ᵐ ω ∂P, N ω ≠ ⊤ := by
    simpa only [N] using
      (avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
        X hFinite T)
  filter_upwards [hNfinite] with ω hN
  intro k t ht
  obtain ⟨F, hF, _⟩ :=
    avram_ja18j_public_original_compensated_finsum X k t ω
  refine ⟨F, hF, ?_⟩
  let B : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((k : ℝ) + 1))}
  have hB : B.Finite :=
    avram_wave7_06_original_negative_band_marked_times_finite X ω T k
  have hFB : F ⊆ hB.toFinset := by
    intro u hu
    rw [Set.Finite.mem_toFinset]
    have hu' := (hF u).mp hu
    exact ⟨hu'.1, hu'.2.1.trans ht, hu'.2.2.2⟩
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hneg : -(1 / ((k : ℝ) + 1)) < 0 := by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) :=
      div_pos (by norm_num) hk
    linarith
  have hbandLe :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1)))) ≤ N ω := by
    apply measure_mono
    rintro ⟨u, z⟩ ⟨hu, hz⟩
    exact ⟨hu, lt_of_le_of_lt hz hneg⟩
  have hcount :=
    avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
      X ω T k
  rw [Set.ncard_eq_toFinset_card _ hB] at hcount
  have hcard : (F.card : ℝ≥0∞) ≤ N ω := by
    calc
      (F.card : ℝ≥0∞) ≤ (hB.toFinset.card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_le_card hFB
      _ = _ := hcount.symm
      _ ≤ N ω := hbandLe
  have hreal := ENNReal.toReal_mono hN hcard
  simpa only [ENNReal.toReal_natCast] using hreal
