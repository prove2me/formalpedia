-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_disjoint_negative_borel_real_count_add_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:52:27.260953+00:00
-- url     : https://prove2.me/submissions/7a6a7d72-17b7-4fea-9fa7-48682a43fbd4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_ja34_original_all_negative_borel_expected_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hNegA : A ⊆ Iio (0 : ℝ)) (hNegB : B ⊆ Iio (0 : ℝ))
    (hDisj : Disjoint A B) :
    let N : Set ℝ → Ω → ℝ≥0∞ := fun C ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ C)
    ∀ᵐ ω ∂P, (N (A ∪ B) ω).toReal =
      (N A ω).toReal + (N B ω).toReal := by
  let N : Set ℝ → Ω → ℝ≥0∞ := fun C ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ C)
  change ∀ᵐ ω ∂P, (N (A ∪ B) ω).toReal =
    (N A ω).toReal + (N B ω).toReal
  have hFin (C : Set ℝ) (hC : MeasurableSet C)
      (hNeg : C ⊆ Iio (0 : ℝ)) : ∀ᵐ ω ∂P, N C ω < ⊤ := by
    have hRate : X.ν C < ⊤ :=
      lt_of_le_of_lt (measure_mono hNeg) (lt_top_iff_ne_top.mpr hFinite)
    apply avram_p2_e_compensator_finite_nu_count_ae_finite
      X 0 T (show (0 : ℝ≥0) ≤ T from zero_le) C hC hRate
    simpa only [tsub_zero, N] using
      avram_ja34_original_all_negative_borel_expected_count_exact
        X T C hC hNeg
  filter_upwards [hFin A hA hNegA, hFin B hB hNegB] with ω ha hb
  have hu : N (A ∪ B) ω = N A ω + N B ω := by
    simpa only [N] using
      (avram_p4_b_smalljump_original_intrinsic_disjoint_mark_band_union_additive
        X 0 T A B hA hB hDisj ω)
  rw [hu, ENNReal.toReal_add (ne_of_lt ha) (ne_of_lt hb)]
