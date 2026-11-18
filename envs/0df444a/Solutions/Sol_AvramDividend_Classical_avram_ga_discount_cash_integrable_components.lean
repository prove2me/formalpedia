-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_discount_cash_integrable_components
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-11-18T00:42:39.876794+00:00
-- url     : https://prove2.me/submissions/a675d0c3-a837-494c-a995-c20423706022

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution : ¬ (∀
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (F Occ Z : Ω → ℝ) (a b c : ℝ)
    (hFI : Integrable F μ) (hOcc : Integrable Occ μ)
    (hZI : Integrable Z μ),
    Integrable (fun ω => F ω - a - (b + c * Occ ω) - Z ω) μ) := by
  classical
  intro h
  let Ω := ℕ
  letI : MeasurableSpace Ω := ⊤
  let μ : Measure Ω := Measure.count
  let Z : Ω → ℝ := fun _ => 0
  have hz : Integrable Z μ := by simp [Z]
  have hc := h (Ω := Ω) μ Z Z Z (1 : ℝ) (0 : ℝ) (0 : ℝ) hz hz hz
  have hMinus : Integrable (fun _ : Ω => (-1 : ℝ)) μ := by
    simpa [Z] using hc
  have hFinite : IsFiniteMeasure μ :=
    (integrable_const_iff_isFiniteMeasure
      (by norm_num : (-1 : ℝ) ≠ 0)).mp hMinus
  have hInf : (Set.univ : Set Ω).Infinite := Set.infinite_univ
  have hPinf : μ Set.univ = ⊤ := Measure.count_apply_infinite hInf
  letI : IsFiniteMeasure μ := hFinite
  have hPlt : μ Set.univ < ⊤ := measure_lt_top μ Set.univ
  rw [hPinf] at hPlt
  exact (lt_irrefl _ hPlt)
