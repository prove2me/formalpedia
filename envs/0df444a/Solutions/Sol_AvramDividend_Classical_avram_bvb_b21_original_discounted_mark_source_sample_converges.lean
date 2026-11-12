-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_original_discounted_mark_source_sample_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:47:26.870197+00:00
-- url     : https://prove2.me/submissions/1da9b05d-f30c-40db-8296-018be11a6a62

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The discounted mark rate converges along bounded samples approaching from below. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, X.ν {a} = 0) (q : ℝ)
    (s : ℕ → ℝ≥0) (hs_tend : Tendsto s atTop (𝓝 t))
    (hs_le : ∀ n, s n ≤ t) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    (∀ᶠ n in atTop, 0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C) →
    Tendsto (fun n => Real.exp (-(q * (s n : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U (s n) + z) - w (U (s n)) ∂X.ν)
      atTop (𝓝 (Real.exp (-(q * (t : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν)) := by
  intro U hCap hEventually
  let A : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
  have hCont := avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
    X x C D hD ω S t ht htpos hsource hFinite
    w hw_cont hw_neg hw_meas hActivity hνatom q hCap
  have hPos : ∀ᶠ n in atTop, 0 < s n :=
    hs_tend.eventually (eventually_gt_nhds htpos)
  have hMem : ∀ᶠ n in atTop, s n ∈ (Ioc 0 t ∩ U ⁻¹' A) := by
    filter_upwards [hPos, hEventually] with n hn hp
    exact ⟨⟨hn, hs_le n⟩, hp⟩
  have hsWithin : Tendsto s atTop (𝓝[Ioc 0 t ∩ U ⁻¹' A] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs_tend, hMem⟩
  exact hCont.tendsto.comp hsWithin
