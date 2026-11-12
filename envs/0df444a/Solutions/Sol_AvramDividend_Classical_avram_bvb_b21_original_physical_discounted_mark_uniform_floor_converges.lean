-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_original_physical_discounted_mark_uniform_floor_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:44:06.587266+00:00
-- url     : https://prove2.me/submissions/203905c5-385a-44ff-b2d5-983b48493230

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hpre : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q T : ℝ) (hT : 0 < T) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    Tendsto (fun n => Real.exp (-(q * (s n : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U (s n) + z) - w (U (s n)) ∂X.ν)
      atTop (𝓝 (Real.exp (-(q * (t : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν)) := by
  let v : ℕ → ℝ := fun n => T *
    (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2)
  let s : ℕ → ℝ≥0 := fun n => Real.toNNReal (v n)
  have hfloor := avram_bvb_b21_original_uniform_floor_samples_converge_from_left T (t : ℝ) hT t.property
  have hn (n : ℕ) : 0 ≤ v n := by
    dsimp [v]
    positivity
  have hs_le (n : ℕ) : s n ≤ t := by
    apply NNReal.coe_le_coe.mp
    simpa only [s, v, Real.coe_toNNReal _ (hn n)] using hfloor.1 n
  have hs_tend : Tendsto s atTop (𝓝 t) := by
    have hc := (continuous_real_toNNReal.tendsto (t : ℝ)).comp hfloor.2
    rw [Real.toNNReal_coe] at hc
    change Tendsto (Real.toNNReal ∘ v) atTop (𝓝 t)
    exact hc
  have hwm : Measurable w :=
    avram_wave6_04b_cap_extension_measurable_of_zero_negative
      w w (⊤ : ℝ≥0∞) hw_cont hw_neg
      (by intro _ y; rfl) (by intro h; exact (h rfl).elim)
  have hνatom (z : ℝ) : X.ν ({z} : Set ℝ) = 0 :=
    avram_bvb_phys107_Standing_BV_negative_mark_singletons_null X hX hBV z
  have htcap := avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
    X x C hxc D hD ω t (Or.inr hpre)
  have hscap (n : ℕ) :=
    avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
      X x C hxc D hD ω (s n)
      (Or.inr (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr (hs_le n)) hpre))
  have hspos : ∀ᶠ n in atTop, 0 < s n :=
    hs_tend.eventually (Ioi_mem_nhds htpos)
  have hsvalid : ∀ᶠ n in atTop,
      s n ∈ Ioc 0 t ∩ (fun r : ℝ≥0 => Function.leftLim
        (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r) ⁻¹'
          {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} := by
    filter_upwards [hspos] with n hn'
    exact ⟨⟨hn', hs_le n⟩, hscap n⟩
  have hswithin : Tendsto s atTop
      (𝓝[Ioc 0 t ∩ (fun r : ℝ≥0 => Function.leftLim
        (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r) ⁻¹'
          {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs_tend, hsvalid⟩
  exact (avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
    X x C D hD ω S t ht htpos hsource hFinite w hw_cont hw_neg
    hwm hActivity hνatom q htcap).tendsto.comp hswithin
