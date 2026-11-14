-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a167_masked_positive_C2_gaussian_source_residual_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:41:03.346017+00:00
-- url     : https://prove2.me/submissions/eaa75340-979a-42c7-8c77-38911f9d38c5

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

/-- A genuine finite masked Gaussian C2 residual is measurable whenever the
original observed source endpoints remain in its positive smoothness domain. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ)
    (hw0 : ContinuousOn w (Ioi (0 : ℝ)))
    (hw1 : ContinuousOn (deriv w) (Ioi (0 : ℝ)))
    (hw2 : ContinuousOn (iteratedDeriv 2 w) (Ioi (0 : ℝ)))
    (m : ℕ)
    (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (hA : ∀ i, MeasurableSet {ω | A i ω})
    (Y R : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i))
    (hR : ∀ i, Measurable (R i))
    (hPos : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      A i ω → 0 < Y i ω ∧ 0 < Y i ω + R i ω)
    (d c σ : ℝ) (E0 E1 : ℕ → ℝ) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range m, if A i ω then
        E1 i * (w (Y i ω + R i ω) - w (Y i ω)) -
        (E0 i * (deriv w (Y i ω) * (R i ω - d * c) +
          (iteratedDeriv 2 w (Y i ω) / 2) *
            ((R i ω - d * c)^2 - d * σ^2)) +
          d * E0 i * (σ^2 / 2 * iteratedDeriv 2 w (Y i ω) +
            c * deriv w (Y i ω)))
        else 0) P := by
  classical
  let W0 : ℝ → ℝ := fun y => if 0 < y then w y else 0
  let W1 : ℝ → ℝ := fun y => if 0 < y then deriv w y else 0
  let W2 : ℝ → ℝ := fun y => if 0 < y then iteratedDeriv 2 w y else 0
  have hW0 : Measurable W0 :=
    hw0.measurable_piecewise continuousOn_const isOpen_Ioi.measurableSet
  have hW1 : Measurable W1 :=
    hw1.measurable_piecewise continuousOn_const isOpen_Ioi.measurableSet
  have hW2 : Measurable W2 :=
    hw2.measurable_piecewise continuousOn_const isOpen_Ioi.measurableSet
  let F : ℕ → Ω → ℝ := fun i ω =>
    E1 i * (W0 (Y i ω + R i ω) - W0 (Y i ω)) -
    (E0 i * (W1 (Y i ω) * (R i ω - d * c) +
      (W2 (Y i ω) / 2) * ((R i ω - d * c)^2 - d * σ^2)) +
      d * E0 i * (σ^2 / 2 * W2 (Y i ω) + c * W1 (Y i ω)))
  have hFm (i : ℕ) : Measurable (F i) := by
    have hmY : Measurable (Y i) := hY i
    have hmR : Measurable (R i) := hR i
    have hmZ : Measurable (fun ω => Y i ω + R i ω) := hmY.add hmR
    have hmW0Y : Measurable (fun ω => W0 (Y i ω)) := hW0.comp hmY
    have hmW0Z : Measurable (fun ω => W0 (Y i ω + R i ω)) :=
      hW0.comp hmZ
    have hmW1Y : Measurable (fun ω => W1 (Y i ω)) := hW1.comp hmY
    have hmW2Y : Measurable (fun ω => W2 (Y i ω)) := hW2.comp hmY
    dsimp [F]
    fun_prop (disch := assumption)
  let H : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m, if A i ω then F i ω else 0
  have hHm : Measurable H := by
    dsimp [H]
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hA i) (hFm i) measurable_const
  have hEq : ∀ᵐ ω ∂P, H ω =
      (∑ i ∈ Finset.range m, if A i ω then
        E1 i * (w (Y i ω + R i ω) - w (Y i ω)) -
        (E0 i * (deriv w (Y i ω) * (R i ω - d * c) +
          (iteratedDeriv 2 w (Y i ω) / 2) *
            ((R i ω - d * c)^2 - d * σ^2)) +
          d * E0 i * (σ^2 / 2 * iteratedDeriv 2 w (Y i ω) +
            c * deriv w (Y i ω)))
        else 0) := by
    filter_upwards [hPos] with ω hω
    dsimp [H]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : A i ω
    · obtain ⟨hy,hz⟩ := hω i hi ha
      simp only [if_pos ha]
      simp only [F,W0,W1,W2,if_pos hy,if_pos hz]
    · simp only [if_neg ha]
  exact hHm.aestronglyMeasurable.congr hEq
