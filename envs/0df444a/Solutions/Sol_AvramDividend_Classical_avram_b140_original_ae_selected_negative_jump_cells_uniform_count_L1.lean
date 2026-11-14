-- Prove2me | solution 1 for AvramDividend.Classical.avram_b140_original_ae_selected_negative_jump_cells_uniform_count_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:00:43.355823+00:00
-- url     : https://prove2.me/submissions/a58465fb-5782-488c-8878-575d7abb0c4c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative jump-count intensity bounds selected grid cells with only conull source count domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A : Set Ω)
    (J : Ω → Finset ℕ)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal) :
    Integrable (fun ω => ((J ω).card : ℝ)) P ∧
    (∫ ω in A, ((J ω).card : ℝ) ∂P) ≤
      ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by 
  classical
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ))
  obtain ⟨hNI, hNmean⟩ :=
    avram_ja35_original_negative_borel_real_count_first_moment
      X hFinite T (Iio (0 : ℝ)) measurableSet_Iio (Subset.refl _)
  dsimp only at hNI hNmean
  have hJI : Integrable (fun ω => ((J ω).card : ℝ)) P := by
    apply hNI.mono_nonneg hJmeas.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _)
    · exact hJdom
  refine ⟨hJI, ?_⟩
  calc
    (∫ ω in A, ((J ω).card : ℝ) ∂P) ≤
        ∫ ω, ((J ω).card : ℝ) ∂P := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _))
        hJI
    _ ≤ ∫ ω, (N ω).toReal ∂P := by
      exact integral_mono_ae hJI hNI hJdom
    _ = ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := hNmean
