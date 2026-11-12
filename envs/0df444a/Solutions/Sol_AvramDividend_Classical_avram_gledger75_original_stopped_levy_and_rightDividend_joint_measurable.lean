-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:56:16.949627+00:00
-- url     : https://prove2.me/submissions/202c326c-c3a2-4a81-ae07-9466be6ec155

import Mathlib
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Extract ambient measurability of a finite-valued original stopping clock
    in a context containing only the filtration and the clock. -/
private theorem gaussianA_original_clock_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    Measurable (fun ω : Ω => (ρ ω : WithTop ℝ≥0)) :=
  hρstop.measurable.mono hρstop.measurableSpace_le le_rfl

/-- Convert the measurable original finite stopping clock from WithTop to
    NNReal before introducing the Lévy process or dividend regularity. -/
private theorem gaussianA_original_clock_nnreal_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) : Measurable ρ :=
  measurable_coe_nnreal_ennreal_iff.mp
    (gaussianA_original_clock_measurable ρ hρstop)

/- Original stopped Lévy and right-dividend coordinates are measurable by
    composing genuine jointly measurable paths with the clipped clock. -/
set_option maxHeartbeats 8000000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (Δ : ℝ≥0) :
    ∀ i : ℕ,
      Measurable (fun ω => X.X (min ((i : ℝ≥0) * Δ) (ρ ω)) ω) ∧
      Measurable (fun ω => rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω) := by
  have hρ : Measurable ρ :=
    gaussianA_original_clock_nnreal_measurable ρ hρstop
  have hXjoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation X.X
      (fun t => (X.adapted t).mono (𝓕.le t) le_rfl) X.rightCont
  have hDjoint : Measurable (fun z : ℝ≥0 × Ω => rightLimit D z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation
      (rightLimit D)
      (dividendStrategy_rightLimit_measurable D hD)
      (dividendStrategy_rightLimit_rightContinuous D hD)
  intro i
  have hv : Measurable (fun ω : Ω => min ((i : ℝ≥0) * Δ) (ρ ω)) :=
    measurable_const.min hρ
  have hp : Measurable (fun ω : Ω =>
      (min ((i : ℝ≥0) * Δ) (ρ ω), ω)) :=
    hv.prod measurable_id
  exact ⟨hXjoint.comp hp, hDjoint.comp hp⟩
