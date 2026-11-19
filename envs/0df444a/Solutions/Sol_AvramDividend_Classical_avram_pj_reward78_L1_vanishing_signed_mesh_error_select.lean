-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward78_L1_vanishing_signed_mesh_error_select
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:53:44.219287+00:00
-- url     : https://prove2.me/submissions/d5fbc7ae-061f-4359-a28a-c2950f28a6d9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ℝ) (E R : ℕ → Ω → ℝ)
    (hEI : ∀ k, Integrable (E k) P)
    (hR : ∀ k, ∀ᵐ ω ∂P, R k ω ≤ 0)
    (hLedger : ∀ k, ∀ᵐ ω ∂P, F ω ≤ E k ω + R k ω)
    (hVan : Tendsto (fun k => ∫ ω, |E k ω| ∂P)
      Filter.atTop (𝓝 (0 : ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ e r : Ω → ℝ,
      Integrable e P ∧
      (∫ ω, |e ω| ∂P) ≤ ε ∧
      (∀ᵐ ω ∂P, r ω ≤ 0) ∧
      (∀ᵐ ω ∂P, F ω ≤ e ω + r ω) := by
  have hEventually : ∀ᶠ k : ℕ in Filter.atTop,
      (∫ ω, |E k ω| ∂P) < ε :=
    (tendsto_order.1 hVan).2 ε hε
  obtain ⟨k, hk⟩ := hEventually.exists
  exact ⟨E k, R k, hEI k, le_of_lt hk, hR k, hLedger k⟩
