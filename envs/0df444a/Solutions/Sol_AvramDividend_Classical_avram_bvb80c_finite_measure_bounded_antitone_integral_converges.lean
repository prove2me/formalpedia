-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb80c_finite_measure_bounded_antitone_integral_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:28:07.784984+00:00
-- url     : https://prove2.me/submissions/8c696ed6-0273-48b8-9580-ea5cf311205b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (f : ℕ → α → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hMeas : ∀ n, Measurable (f n))
    (hBound : ∀ n a, ‖f n a‖ ≤ K)
    (hAnti : ∀ n m, n ≤ m → ∀ a, f m a ≤ f n a) :
    ∃ v : ℝ, Tendsto (fun n : ℕ => ∫ a, f n a ∂μ)
      atTop (𝓝 v) := by
  classical
  have hInt (n : ℕ) : Integrable (f n) μ := by
    have hSM : AEStronglyMeasurable (f n) μ :=
      (hMeas n).aestronglyMeasurable
    exact Integrable.of_bound hSM K
      (Filter.Eventually.of_forall (hBound n))
  have hIntegralBound (n : ℕ) :
      ‖∫ a, f n a ∂μ‖ ≤ K * μ.real Set.univ :=
    norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall (hBound n))
  have hAntitoneIntegral : Antitone
      (fun n : ℕ => ∫ a, f n a ∂μ) := by
    intro n m hnm
    exact integral_mono (hInt m) (hInt n)
      (hAnti n m hnm)
  have hBelow : BddBelow
      (Set.range (fun n : ℕ => ∫ a, f n a ∂μ)) := by
    refine ⟨-(K * μ.real Set.univ), ?_⟩
    rintro v ⟨n, rfl⟩
    exact (neg_le_of_abs_le (by
      simpa only [Real.norm_eq_abs] using hIntegralBound n))
  exact Real.tendsto_of_bddBelow_antitone hBelow hAntitoneIntegral
