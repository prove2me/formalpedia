-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb25_original_zero_contact_stopped_K_negative_mark_integrand_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:51:28.176365+00:00
-- url     : https://prove2.me/submissions/9e1c1e14-04f1-4663-ac5d-39adebf7649f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S)
    (hnb : (nhdsWithin t (Iio t)).NeBot)
    (hSource : ∀ s : ℝ≥0, s ≤ S →
      X.X s ω = (s : ℝ) * X.drift)
    (hZero : ∀ s : ℝ≥0, s ≤ S →
      riskProcess X x D s ω = 0)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (q T δ : ℝ) (z : ℝ)
    (htpos : 0 < t)
    (htPrefix : (t : ℝ) < T - δ)
    (htStop : (t : ℝ≥0∞) ≤ ruinTime X x D ω)
    (hz : z < 0) :
    (if 0 < t ∧ (t : ℝ) < T - δ ∧
        (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
        0 ≤ Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
        ENNReal.ofReal (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ C ∧ z < 0 then
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
          w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
      else 0) =
      -(Real.exp (-(q * (t : ℝ))) * w 0)  := by
  have hU :=
    avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
      X x C D hD ω S t ht hnb hSource hZero
  simp [hU, htpos, htPrefix, htStop, hz, hw_neg z hz] <;> ring
