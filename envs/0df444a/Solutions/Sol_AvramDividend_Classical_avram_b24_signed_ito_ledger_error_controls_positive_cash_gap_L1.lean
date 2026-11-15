-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_signed_ito_ledger_error_controls_positive_cash_gap_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:26:35.745291+00:00
-- url     : https://prove2.me/submissions/b86fef49-4ebb-414e-9618-a434b7d0f9ab

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F G J E : Ω → ℝ) (b : ℝ)
    (hFI : Integrable F P) (hGI : Integrable G P)
    (hJI : Integrable J P) (hEI : Integrable E P)
    (hLedger : ∀ᵐ ω ∂P, F ω ≤ b + G ω + J ω + E ω) :
    Integrable (fun ω => max 0 (F ω - b - G ω - J ω)) P ∧
    (∫ ω, ‖max 0 (F ω - b - G ω - J ω)‖ ∂P) ≤
      ∫ ω, ‖E ω‖ ∂P := by
  have hdM : AEStronglyMeasurable
      (fun ω => F ω - b - G ω - J ω) P := by
    exact (((hFI.aestronglyMeasurable.sub aestronglyMeasurable_const).sub
      hGI.aestronglyMeasurable).sub hJI.aestronglyMeasurable)
  have hpM : AEStronglyMeasurable
      (fun ω => max 0 (F ω - b - G ω - J ω)) P := by
    convert (aestronglyMeasurable_const.sup hdM) using 1
    funext ω
    rfl
  have hpLe : (fun ω => max 0 (F ω - b - G ω - J ω)) ≤ᵐ[P]
      (fun ω => ‖E ω‖) := by
    filter_upwards [hLedger] with ω hω
    have he : E ω ≤ ‖E ω‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (E ω)
    apply max_le (norm_nonneg _)
    linarith
  have hpNonneg : (fun _ : Ω => (0 : ℝ)) ≤ᵐ[P]
      (fun ω => max 0 (F ω - b - G ω - J ω)) :=
    Filter.Eventually.of_forall (fun ω => le_max_left _ _)
  have hpI : Integrable (fun ω => max 0 (F ω - b - G ω - J ω)) P :=
    integrable_of_le_of_le hpM hpNonneg hpLe (integrable_zero Ω ℝ P) hEI.norm
  refine ⟨hpI, ?_⟩
  have hpN : ∀ ω, 0 ≤ max 0 (F ω - b - G ω - J ω) :=
    fun ω => le_max_left _ _
  have hpEq : (fun ω => ‖max 0 (F ω - b - G ω - J ω)‖) =
      (fun ω => max 0 (F ω - b - G ω - J ω)) := by
    funext ω
    exact Real.norm_of_nonneg (hpN ω)
  rw [hpEq]
  exact integral_mono_ae hpI hEI.norm hpLe
