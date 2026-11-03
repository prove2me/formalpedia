-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_integrable_signed_measurable_antitone_set_tails_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:37:21.108115+00:00
-- url     : https://prove2.me/submissions/6ff4e792-0dcb-4c0e-8319-51f130b81e6f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

/-- An integrable signed real kernel has zero integral over antitone measurable vanishing tails. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ)
    (hf : Integrable f μ)
    (S : ℕ → Set α) (hSm : ∀ n, MeasurableSet (S n))
    (hAnti : Antitone S) (hEmpty : (⋂ n, S n) = ∅) :
    Tendsto (fun n : ℕ => ∫ x, (S n).indicator f x ∂μ)
      atTop (𝓝 0) := by
  classical
  have hmeas (n : ℕ) :
      AEStronglyMeasurable ((S n).indicator f) μ :=
    (hf.indicator (hSm n)).aestronglyMeasurable
  have hbound (n : ℕ) :
      ∀ᵐ x ∂μ, ‖(S n).indicator f x‖ ≤ ‖f x‖ := by
    filter_upwards [] with x
    by_cases hx : x ∈ S n <;> simp [Set.indicator, hx]
  have hpoint (x : α) :
      Tendsto (fun n : ℕ => (S n).indicator f x) atTop (𝓝 0) := by
    have hnot : ∃ N : ℕ, x ∉ S N := by
      by_contra h
      push_neg at h
      have hx : x ∈ ⋂ n, S n := Set.mem_iInter.mpr h
      simpa [hEmpty] using hx
    obtain ⟨N, hN⟩ := hnot
    have hevent : ∀ᶠ n : ℕ in atTop, x ∉ S n := by
      filter_upwards [eventually_ge_atTop N] with n hn
      intro hx
      exact hN (hAnti hn hx)
    have heq : (fun n : ℕ => (S n).indicator f x) =ᶠ[atTop]
        fun _ => (0 : ℝ) := by
      filter_upwards [hevent] with n hn
      simp [Set.indicator, hn]
    exact tendsto_const_nhds.congr' heq.symm
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence
      (fun x => ‖f x‖) hmeas hf.norm hbound
      (Filter.Eventually.of_forall hpoint)