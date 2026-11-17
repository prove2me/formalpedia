-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_Borel_physical_grid_prefix_tuple_filtration_measurable_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:08:38.707112+00:00
-- url     : https://prove2.me/submissions/8c188e97-74fd-45f5-89d2-2b5fb1f918b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℝ≥0 := T / (n : ℝ≥0)
    ∀ k : ℕ, k ≤ n →
      Measurable[𝓕 ((k : ℝ≥0) * δ)] (fun ω : Ω =>
        fun i : Fin k => NX ω (Ioc ((i.val : ℝ≥0) * δ)
          (((i.val + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B)) := by
  classical
  dsimp only
  intro k hk
  let C : Ω → Fin k → ℝ≥0∞ :=
    fun ω : Ω => fun i : Fin k =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc ((i.val : ℝ≥0) * (T / (n : ℝ≥0)))
          (((i.val + 1 : ℕ) : ℝ≥0) * (T / (n : ℝ≥0))) ×ˢ B)
  have hCoords : ∀ i : Fin k,
      Measurable[𝓕 ((k : ℝ≥0) * (T / (n : ℝ≥0)))]
        (fun ω : Ω => C ω i) := by
    intro i
    have hi : i.val + 1 ≤ k := Nat.succ_le_iff.mpr i.isLt
    have hEnd :
        (((i.val + 1 : ℕ) : ℝ≥0) * (T / (n : ℝ≥0))) ≤
          (k : ℝ≥0) * (T / (n : ℝ≥0)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hi) bot_le
    have hCell :=
      avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
        X ((i.val : ℝ≥0) * (T / (n : ℝ≥0)))
          (((i.val + 1 : ℕ) : ℝ≥0) * (T / (n : ℝ≥0))) B hB
    have hAdapt := hCell.mono (𝓕.mono hEnd) le_rfl
    simpa only [C] using hAdapt
  letI : MeasurableSpace Ω := 𝓕 ((k : ℝ≥0) * (T / (n : ℝ≥0)))
  change Measurable C
  exact measurable_pi_lambda C hCoords
