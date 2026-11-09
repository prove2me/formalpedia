-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_uniform_jump_gap_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T20:04:37.43796+00:00
-- url     : https://prove2.me/submissions/831cd2f0-5bcb-4f0b-a1c4-46f6e3eb035b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_jump_tsum_finite_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every finite family of nonzero real marks has a positive absolute gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ u : ℝ≥0, 0 < u → u ≤ T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
          ε ≤ |X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u| := by
  classical
  have hMin :
      ∀ F : Finset ℝ≥0, ∀ j : ℝ≥0 → ℝ,
        (∀ u ∈ F, j u ≠ 0) →
          ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ F, ε ≤ |j u| := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
        intro j hj
        refine ⟨1, by norm_num, ?_⟩
        intro u hu
        simp at hu
    | @insert a F ha ih =>
        intro j hj
        have hja : j a ≠ 0 := hj a (Finset.mem_insert_self _ _)
        have hjF : ∀ u ∈ F, j u ≠ 0 := by
          intro u hu
          exact hj u (Finset.mem_insert_of_mem hu)
        obtain ⟨ε, hε, hεF⟩ := ih j hjF
        refine ⟨min ε |j a|, lt_min hε (abs_pos.mpr hja), ?_⟩
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hεF u hu)
  have hAll := avram_ubv_mixed12_original_jump_tsum_finite_ae X hFinite
  filter_upwards [hAll] with ω hω
  intro T
  obtain ⟨F, hF, _⟩ := hω T
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hj : ∀ u ∈ F, j u ≠ 0 := by
    intro u hu
    exact ((hF u).mp hu).2.2
  obtain ⟨ε, hε, hεF⟩ := hMin F j hj
  refine ⟨ε, hε, ?_⟩
  intro u hu0 huT hju
  exact hεF u ((hF u).mpr ⟨hu0, huT, hju⟩)
