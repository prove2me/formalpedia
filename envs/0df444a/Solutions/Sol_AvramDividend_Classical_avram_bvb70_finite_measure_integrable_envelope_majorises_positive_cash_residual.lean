-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb70_finite_measure_integrable_envelope_majorises_positive_cash_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:46:59.4752+00:00
-- url     : https://prove2.me/submissions/1dcea946-6f21-4aec-b84f-b3b04be45c3b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology
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
  intro E
  let Henv : Ω → ℝ := fun ω => Fbound ω + Jbound ω + Vbound ω + |b|
  refine ⟨Henv, ?_, ?_, ?_⟩
  · exact (((hFi.add hJi).add hVi).add (integrable_const |b|))
  · intro n
    change AEStronglyMeasurable
      (fun ω => max (F n ω - (b + (J n ω - V n ω))) 0) P
    exact ((hFRows n).aestronglyMeasurable.sub
      (aestronglyMeasurable_const.add
        ((hJRows n).aestronglyMeasurable.sub
          (hVRows n).aestronglyMeasurable))).sup aestronglyMeasurable_const
  · intro n
    filter_upwards [hFdom n, hJdom n, hVdom n] with ω hf hj hv
    change ‖max (F n ω - (b + (J n ω - V n ω))) 0‖ ≤
      Fbound ω + Jbound ω + Vbound ω + |b|
    rw [Real.norm_eq_abs] at hf hj hv ⊢
    have harg : F n ω - (b + (J n ω - V n ω)) ≤
        Fbound ω + Jbound ω + Vbound ω + |b| := by
      linarith [(abs_le.mp hf).2, (abs_le.mp hj).1,
        (abs_le.mp hv).2, neg_le_abs b]
    have henv : 0 ≤ Fbound ω + Jbound ω + Vbound ω + |b| := by
      linarith [abs_nonneg (F n ω), abs_nonneg (J n ω),
        abs_nonneg (V n ω), abs_nonneg b]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le harg henv
