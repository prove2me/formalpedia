-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_ae_signed_mesh_error_vanish_implies_cash_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:27:26.744205+00:00
-- url     : https://prove2.me/submissions/3e6c2b36-9228-4279-adcc-cd7a5643f010

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section
/-- An a.e. signed mesh ledger with vanishing errors implies the limiting upper inequality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (F G J : Ω → ℝ) (c : ℝ)
    (B E : ℕ → Ω → ℝ)
    (hB : ∀ᵐ ω ∂(P.restrict A), ∀ m : ℕ, B m ω ≤ 0)
    (hE : ∀ᵐ ω ∂(P.restrict A),
      Tendsto (fun m => E m ω) atTop (nhds (0 : ℝ)))
    (hCash : ∀ᵐ ω ∂(P.restrict A), ∀ m : ℕ,
      F ω ≤ c + G ω + J ω + B m ω + E m ω) :
    ∀ᵐ ω ∂(P.restrict A), F ω ≤ c + G ω + J ω := by
  filter_upwards [hB, hE, hCash] with ω hBω hEω hCashω
  have hUpper (m : ℕ) :
      F ω ≤ c + G ω + J ω + E m ω := by
    have hSign := hBω m
    have hBound := hCashω m
    linarith
  have hConvergence :
      Tendsto (fun m => c + G ω + J ω + E m ω)
        atTop (nhds (c + G ω + J ω)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hEω :
        Tendsto (fun m => (c + G ω + J ω) + E m ω)
          atTop (nhds ((c + G ω + J ω) + 0)))
  exact ge_of_tendsto hConvergence
    (Filter.Eventually.of_forall hUpper)
