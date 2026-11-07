-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f6_gaussian_zero_discount_scale_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:34:24.69272+00:00
-- url     : https://prove2.me/submissions/5f5797d0-11d5-4ff2-b3fb-0a322e0fcfd4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_ladder_renewal_measure_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_atomless_continuous
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_exponential_tonelli

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ) :
    ∃ W₀ : ℝ → ℝ, IsScaleFunction X 0 W₀ := by
  obtain ⟨ν, hSupp, hAtom, hFin, hLap⟩ :=
    avram_p4_f6_gaussian_zero_ladder_renewal_measure_exists X hX hσ
  let W₀ : ℝ → ℝ :=
    fun x => if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0
  refine ⟨W₀, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    simp only [W₀, not_le.mpr hy, ↓reduceIte]
  · intro y hy
    simpa only [W₀, if_pos hy] using
      (ENNReal.toReal_nonneg : 0 ≤ (ν (Ioc (0 : ℝ) y)).toReal)
  · exact avram_p4_f6_renewal_cdf_atomless_continuous ν hAtom hFin
  · intro x hx y hy hxy
    have hle : ν (Ioc (0 : ℝ) x) ≤ ν (Ioc (0 : ℝ) y) := by
      apply measure_mono
      intro z hz
      exact ⟨hz.1, le_trans hz.2 hxy⟩
    have hx0 : (0 : ℝ) ≤ x := Set.mem_Ici.mp hx
    have hy0 : (0 : ℝ) ≤ y := Set.mem_Ici.mp hy
    change (if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0) ≤
      (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0)
    rw [if_pos hx0, if_pos hy0]
    exact ENNReal.toReal_mono (ne_of_lt (hFin y hy0)) hle
  · intro θ hθ hψ
    have h := avram_p4_f6_renewal_cdf_exponential_tonelli
      X hX hσ ν hSupp hFin hLap θ hθ hψ
    simpa only [W₀, sub_zero] using h
