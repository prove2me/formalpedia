-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb74_finite_measure_component_envelopes_compensated_positive_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:44:53.668885+00:00
-- url     : https://prove2.me/submissions/d2a79801-1921-4b61-9bf4-a2e8d32e9e69

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F J V : ℕ → Ω → ℝ) (b : ℝ)
    (Fbound Jbound Vbound : Ω → ℝ)
    (hFi : Integrable Fbound P) (hJi : Integrable Jbound P)
    (hVi : Integrable Vbound P)
    (hFRows : ∀ n, Integrable (F n) P)
    (hJRows : ∀ n, Integrable (J n) P)
    (hVRows : ∀ n, Integrable (V n) P)
    (hFdom : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ Fbound ω)
    (hJdom : ∀ n, ∀ᵐ ω ∂P, ‖J n ω‖ ≤ Jbound ω)
    (hVdom : ∀ n, ∀ᵐ ω ∂P, ‖V n ω‖ ≤ Vbound ω) :
    let E : ℕ → Ω → ℝ := fun n ω =>
      max (F n ω - (b + (J n ω - V n ω))) 0
    ∃ Henv : Ω → ℝ,
      Integrable Henv P ∧
      (∀ n, AEStronglyMeasurable (E n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, ‖E n ω‖ ≤ Henv ω) := by
  classical
  intro E
  let Henv : Ω → ℝ :=
    fun ω => Fbound ω + Jbound ω + Vbound ω + |b|
  have hHi : Integrable Henv P := by
    change Integrable
      (fun ω => Fbound ω + Jbound ω + Vbound ω + |b|) P
    exact ((hFi.add hJi).add hVi).add (integrable_const _)
  refine ⟨Henv, hHi, ?_, ?_⟩
  · intro n
    have hFA : AEMeasurable (F n) P :=
      (hFRows n).aestronglyMeasurable.aemeasurable
    have hJA : AEMeasurable (J n) P :=
      (hJRows n).aestronglyMeasurable.aemeasurable
    have hVA : AEMeasurable (V n) P :=
      (hVRows n).aestronglyMeasurable.aemeasurable
    have hA : AEMeasurable
        (fun ω => F n ω - (b + (J n ω - V n ω))) P :=
      hFA.sub (aemeasurable_const.add (hJA.sub hVA))
    change AEStronglyMeasurable
      (fun ω => max (F n ω - (b + (J n ω - V n ω))) 0) P
    exact (hA.max aemeasurable_const).aestronglyMeasurable
  · intro n
    filter_upwards [hFdom n, hJdom n, hVdom n] with ω hFω hJω hVω
    have hFF : F n ω ≤ Fbound ω :=
      (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using hFω)
    have hJJ : -(J n ω) ≤ Jbound ω :=
      (neg_le_abs _).trans (by
        simpa only [Real.norm_eq_abs] using hJω)
    have hVV : V n ω ≤ Vbound ω :=
      (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using hVω)
    have hFB : 0 ≤ Fbound ω := (norm_nonneg _).trans hFω
    have hJB : 0 ≤ Jbound ω := (norm_nonneg _).trans hJω
    have hVB : 0 ≤ Vbound ω := (norm_nonneg _).trans hVω
    have hb : -b ≤ |b| := neg_le_abs _
    have hUpper : F n ω - (b + (J n ω - V n ω)) ≤ Henv ω := by
      dsimp [Henv]
      linarith
    have hNonneg : (0 : ℝ) ≤ Henv ω := by
      dsimp [Henv]
      have : 0 ≤ |b| := abs_nonneg _
      linarith
    have hMax : max (F n ω - (b + (J n ω - V n ω))) 0 ≤
        Henv ω := max_le hUpper hNonneg
    have hPositive : 0 ≤ max (F n ω - (b + (J n ω - V n ω))) 0 :=
      le_max_right _ _
    change ‖max (F n ω - (b + (J n ω - V n ω))) 0‖ ≤ Henv ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg hPositive] using hMax
