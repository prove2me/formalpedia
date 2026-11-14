-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:04:50.534645+00:00
-- url     : https://prove2.me/submissions/f8c7a08e-8c42-4f80-9126-2ac8c55a9620

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_uniform_grid_eventually_excludes_all_final_source_negative_marks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual original source negative-jump counting measure assigns zero
mass to the prescribed terminal uniform-grid strip eventually a.s. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      (Measure.count.restrict
        {t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim
            (fun s : ℝ≥0 => X.X s ω) t ≠ 0})
        (Ioc (u n (n + 1)) S) = 0 := by
  intro S
  have h := avram_bvb45_original_uniform_grid_eventually_excludes_all_final_source_negative_marks
    X hBV hFinite T hT u huniform
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  let A : Set ℝ≥0 := {t : ℝ≥0 | 0 < t ∧
    X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}
  have hEmpty : Ioc (u n (n + 1)) S ∩ A = ∅ := by
    ext t
    constructor
    · intro ht
      have htI : t ∈ Ioc (u n (n + 1)) S := ht.1
      have htA : t ∈ A := ht.2
      have htpos : 0 < t :=
        lt_of_le_of_lt (show (0 : ℝ≥0) ≤ u n (n + 1) from bot_le) htI.1
      have htS : (t : ℝ) ≤ T := by
        have hts : t ≤ S := htI.2
        exact_mod_cast hts
      exact hn t htpos (by exact_mod_cast htI.1) htS htA.2
    · intro ht
      exact False.elim ht
  change (Measure.count.restrict A) (Ioc (u n (n + 1)) S) = 0
  rw [Measure.restrict_apply measurableSet_Ioc]
  rw [hEmpty]
  exact measure_empty
