-- Prove2me | solution 1 for DbarRegularity.lintegral_Ioi_indicator_rpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:48:03.785854+00:00
-- url     : https://prove2.me/submissions/66f00665-c3ec-4bd7-8ec6-ea90d673d36b

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace DbarRegularity

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-- `∫_{t > 0, t ≥ a} s t^(-s-1) dt = a^(-s)` for every `a ∈ [0, ∞]` and `s > 0`
(as a lower Lebesgue integral in `[0, ∞]`, with `0^(-s) = ∞` and `∞^(-s) = 0`). -/
lemma lintegral_Ioi_indicator_rpow_neg (a : ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | a ≤ ENNReal.ofReal t}.indicator
      (fun t => ENNReal.ofReal (s * t ^ (-s - 1))) t = a ^ (-s) := by
  have hS : ∀ b : ℝ≥0∞, MeasurableSet {t : ℝ | b ≤ ENNReal.ofReal t} := fun b =>
    measurableSet_le measurable_const ENNReal.measurable_ofReal
  -- positive finite case
  have fin : ∀ b : ℝ, 0 < b →
      ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal b ≤ ENNReal.ofReal t}.indicator
        (fun t => ENNReal.ofReal (s * t ^ (-s - 1))) t = ENNReal.ofReal (b ^ (-s)) := by
    intro b hb
    rw [lintegral_indicator (hS _), Measure.restrict_restrict (hS _)]
    have hset : {t : ℝ | ENNReal.ofReal b ≤ ENNReal.ofReal t} ∩ Ioi 0 = Ici b := by
      ext t
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_Ici]
      constructor
      · rintro ⟨h1, h2⟩; exact (ENNReal.ofReal_le_ofReal_iff h2.le).1 h1
      · intro h; exact ⟨ENNReal.ofReal_le_ofReal h, hb.trans_le h⟩
    rw [hset, setLIntegral_congr Ioi_ae_eq_Ici.symm]
    have hint : IntegrableOn (fun t : ℝ => s * t ^ (-s - 1)) (Ioi b) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hb).const_mul s
    rw [← ofReal_integral_eq_lintegral_ofReal hint]
    · congr 1
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hb]
      rw [show -s - 1 + 1 = -s by ring]
      field_simp
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => ?_)
      exact mul_nonneg hs.le (Real.rpow_nonneg (hb.trans ht).le _)
  rcases eq_or_ne a ⊤ with rfl | ha
  · rw [ENNReal.top_rpow_of_neg (by linarith)]
    have : {t : ℝ | (⊤ : ℝ≥0∞) ≤ ENNReal.ofReal t} = ∅ := by
      ext t; simp
    rw [this, indicator_empty, lintegral_zero]
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [ENNReal.zero_rpow_of_neg (by linarith)]
    have hlim : Tendsto (fun b : ℝ => ENNReal.ofReal b ^ (-s)) (𝓝[>] 0) (𝓝 ((0 : ℝ≥0∞) ^ (-s))) := by
      have h1 : Tendsto (fun b : ℝ => ENNReal.ofReal b) (𝓝[>] 0) (𝓝 0) := by
        have := (ENNReal.continuous_ofReal.tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using this
      exact (ENNReal.continuous_rpow_const.tendsto 0).comp h1
    rw [ENNReal.zero_rpow_of_neg (by linarith)] at hlim
    refine top_unique (le_of_tendsto hlim ?_)
    filter_upwards [self_mem_nhdsWithin] with b hb
    rw [ENNReal.ofReal_rpow_of_pos hb, ← fin b hb]
    refine lintegral_mono fun t => indicator_le_indicator_of_subset ?_ (fun _ => bot_le) t
    intro t _
    exact (bot_le : (⊥ : ℝ≥0∞) ≤ ENNReal.ofReal t)
  · have hpos : 0 < a.toReal := ENNReal.toReal_pos ha0 ha
    have h := fin a.toReal hpos
    rw [ENNReal.ofReal_toReal ha] at h
    rw [h, ← ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_toReal ha]

end DbarRegularity

open DbarRegularity

open MeasureTheory Set
open scoped ENNReal

theorem solution (a : ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | a ≤ ENNReal.ofReal t}.indicator
      (fun t => ENNReal.ofReal (s * t ^ (-s - 1))) t = a ^ (-s) :=
  lintegral_Ioi_indicator_rpow_neg a hs
