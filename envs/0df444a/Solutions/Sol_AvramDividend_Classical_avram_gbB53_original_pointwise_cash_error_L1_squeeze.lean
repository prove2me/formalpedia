-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB53_original_pointwise_cash_error_L1_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:16:33.684072+00:00
-- url     : https://prove2.me/submissions/3985a47a-68a4-4e0d-877f-fb901636f15c

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω)
    (F B : Ω → ℝ) (M E : ℕ → Ω → ℝ)
    (hSourceI : ∀ m, IntegrableOn
      (fun ω => max (F ω - M m ω - B ω) 0) A P)
    (hErrorI : ∀ m, IntegrableOn
      (fun ω => max (E m ω) 0) A P)
    (hSource : ∀ m, ∀ᵐ ω ∂(P.restrict A),
      F ω - M m ω - B ω ≤ E m ω)
    (hErrorL1 : Tendsto
      (fun m => ∫ ω in A, max (E m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun m => ∫ ω in A, max (F ω - M m ω - B ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hPos (m : ℕ) :
      0 ≤ (∫ ω in A, max (F ω - M m ω - B ω) 0 ∂P) :=
    integral_nonneg (fun ω => le_max_right _ _)
  have hUpper (m : ℕ) :
      (∫ ω in A, max (F ω - M m ω - B ω) 0 ∂P) ≤
      (∫ ω in A, max (E m ω) 0 ∂P) := by
    apply integral_mono_ae (hSourceI m) (hErrorI m)
    filter_upwards [hSource m] with ω hω
    exact max_le_max hω le_rfl
  exact squeeze_zero hPos hUpper hErrorL1
