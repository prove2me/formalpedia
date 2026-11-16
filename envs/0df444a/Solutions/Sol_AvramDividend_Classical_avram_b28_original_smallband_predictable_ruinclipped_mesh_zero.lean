-- Prove2me | solution 1 for AvramDividend.Classical.avram_b28_original_smallband_predictable_ruinclipped_mesh_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:43:27.688703+00:00
-- url     : https://prove2.me/submissions/93f45dcf-5a79-4f33-9ef7-dd92394fcaa8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_band_marks_compensator_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (ω : Ω)
    (hLarge : ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (k : ℕ) (σ : Ω → ℝ≥0)
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (W : ℕ → Ω → ℝ) :
    (∑ i ∈ S, (if σ ω ≤ a i then 0 else W i ω) *
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X k (b i) ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X k (a i) ω)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hb :=
    avram_b27_original_no_small_band_marks_compensator_zero
      X hν ω hLarge k (b i)
  have ha :=
    avram_b27_original_no_small_band_marks_compensator_zero
      X hν ω hLarge k (a i)
  simp [ha, hb]
