-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb25_original_zero_contact_stopped_K_global_mark_guard_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:49:27.728658+00:00
-- url     : https://prove2.me/submissions/e80c10ba-b299-4c15-b0f2-6c4be4d7b8e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb25_original_zero_contact_stopped_K_negative_mark_integrand_exact
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
    (ω : Ω) (T : ℝ) (hT : 0 < T)
    (S : ℝ≥0) (hS : (S : ℝ) = T)
    (hSource : ∀ s : ℝ≥0, s ≤ S →
      X.X s ω = (s : ℝ) * X.drift)
    (hZero : ∀ s : ℝ≥0, s ≤ S →
      riskProcess X x D s ω = 0)
    (w : ℝ → ℝ) (hw_neg : ∀ z < 0, w z = 0)
    (q : ℝ) (n : ℕ) (t : ℝ≥0) (z : ℝ) :
(if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
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
      (if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧ z < 0 then
        -(Real.exp (-(q * (t : ℝ))) * w 0)
       else 0)  := by
  by_cases h : 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
      (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧ z < 0
  · rcases h with ⟨htpos, hPrefix, hStop, hz⟩
    have hDelta : 0 < T / ((n : ℝ) + 2) := by positivity
    have htS : t ≤ S := by
      apply NNReal.coe_le_coe.mp
      rw [hS]
      exact le_of_lt (lt_trans hPrefix (sub_lt_self T hDelta))
    have hnb : (nhdsWithin t (Iio t)).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    have hExact :=
      avram_bvb25_original_zero_contact_stopped_K_negative_mark_integrand_exact
        X x C D hD ω S t htS hnb hSource hZero
        w hw_neg q T (T / ((n : ℝ) + 2)) z
        htpos hPrefix hStop hz
    simpa [htpos, hPrefix, hStop, hz] using hExact
  · have hFalse :
        ¬ (0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
            (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
            0 ≤ Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
            ENNReal.ofReal (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ C ∧
            z < 0) := by
          rintro ⟨hp, hf, hs, _, _, hz⟩
          exact h ⟨hp, hf, hs, hz⟩
    simp [h, hFalse]
