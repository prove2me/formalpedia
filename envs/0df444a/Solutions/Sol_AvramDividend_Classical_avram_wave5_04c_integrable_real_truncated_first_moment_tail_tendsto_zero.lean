-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_integrable_real_truncated_first_moment_tail_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:26:59.724854+00:00
-- url     : https://prove2.me/submissions/70cef1e0-ea84-4763-86c8-9ffd1f1e1663

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (R : Ω → ℝ) (hMeas : Measurable R) (hInt : Integrable R P) :
    Tendsto (fun n : ℕ => ∫ ω, if (n : ℝ) < R ω then R ω else 0 ∂P)
      atTop (nhds 0) := by
  have hmeas (n : ℕ) :
      AEStronglyMeasurable (fun ω => if (n : ℝ) < R ω then R ω else 0) P := by
    have hs : MeasurableSet {ω | (n : ℝ) < R ω} :=
      measurableSet_Ioi.preimage hMeas
    exact (hMeas.ite hs measurable_const).aestronglyMeasurable
  have hbound (n : ℕ) :
      ∀ᵐ ω ∂P, ‖if (n : ℝ) < R ω then R ω else 0‖ ≤ ‖R ω‖ := by
    filter_upwards [] with ω
    split_ifs <;> simp
  have hpoint (ω : Ω) :
      Tendsto (fun n : ℕ => if (n : ℝ) < R ω then R ω else 0)
        atTop (nhds 0) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (R ω)
    have hevent : ∀ᶠ n : ℕ in atTop, ¬ (n : ℝ) < R ω := by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact not_lt.mpr (le_trans hN (by exact_mod_cast hn))
    have heq : (fun n : ℕ => if (n : ℝ) < R ω then R ω else 0) =ᶠ[atTop]
        fun _ => (0 : ℝ) := by
      filter_upwards [hevent] with n hn
      simp [hn]
    exact tendsto_const_nhds.congr' heq.symm
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun ω => ‖R ω‖) hmeas hInt.norm hbound (Filter.Eventually.of_forall hpoint)
