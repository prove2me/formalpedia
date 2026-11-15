-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb70_infinite_count_measure_universe_zero_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:04:27.75658+00:00
-- url     : https://prove2.me/submissions/9aad4955-1daf-4776-b4cd-04181b48b528

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem solution : ¬ (∀
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F J V : ℕ → Ω → ℝ) (b : ℝ)
    (Fbound Jbound Vbound : Ω → ℝ)
    (hFi : Integrable Fbound P) (hJi : Integrable Jbound P)
    (hVi : Integrable Vbound P)
    (hFRows : ∀ n, Integrable (F n) P)
    (hJRows : ∀ n, Integrable (J n) P)
    (hVRows : ∀ n, Integrable (V n) P)
    (hFdom : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ Fbound ω)
    (hJdom : ∀ n, ∀ᵐ ω ∂P, ‖J n ω‖ ≤ Jbound ω)
    (hVdom : ∀ n, ∀ᵐ ω ∂P, ‖V n ω‖ ≤ Vbound ω),
    let E : ℕ → Ω → ℝ := fun n ω =>
      max (F n ω - (b + (J n ω - V n ω))) 0
    ∃ Henv : Ω → ℝ,
      Integrable Henv P ∧
      (∀ n, AEStronglyMeasurable (E n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, ‖E n ω‖ ≤ Henv ω)) := by
  classical
  intro h
  let Ω := ℕ
  letI : MeasurableSpace Ω := ⊤
  let P : Measure Ω := Measure.count
  let Z : ℕ → Ω → ℝ := fun _ _ => 0
  let B : Ω → ℝ := fun _ => 0
  have hz : Integrable B P := by simp [B]
  have hrows : ∀ n : ℕ, Integrable (Z n) P := by
    intro n
    simpa [Z, B] using hz
  have hdom : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖Z n ω‖ ≤ B ω := by
    intro n
    filter_upwards [] with ω
    simp [Z, B]
  obtain ⟨Henv, hHI, _, hEnv⟩ :=
    h (Ω := Ω) P Z Z Z (-1) B B B
      hz hz hz hrows hrows hrows hdom hdom hdom
  have hOneLe : ∀ᵐ ω ∂P, (1 : ℝ) ≤ Henv ω := by
    filter_upwards [hEnv 0] with ω hw
    simpa [Z] using hw
  have hOneDom : ∀ᵐ ω ∂P, ‖(1 : ℝ)‖ ≤ ‖Henv ω‖ := by
    filter_upwards [hOneLe] with ω hw
    simpa only [norm_one, Real.norm_eq_abs] using
      (le_trans hw (le_abs_self (Henv ω)))
  have hOneInt : Integrable (fun _ : Ω => (1 : ℝ)) P :=
    hHI.mono aestronglyMeasurable_const hOneDom
  have hPfinite : IsFiniteMeasure P :=
    (integrable_const_iff_isFiniteMeasure
      (by norm_num : (1 : ℝ) ≠ 0)).mp hOneInt
  have hInf : (Set.univ : Set Ω).Infinite := Set.infinite_univ
  have hPinf : P Set.univ = ⊤ :=
    Measure.count_apply_infinite hInf
  letI : IsFiniteMeasure P := hPfinite
  have hPlt : P Set.univ < ⊤ := measure_lt_top P Set.univ
  rw [hPinf] at hPlt
  exact (lt_irrefl _ hPlt)
