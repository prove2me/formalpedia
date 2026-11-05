-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_continuous_negative_support_cutoff_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:46:57.341839+00:00
-- url     : https://prove2.me/submissions/95fdd6e5-1b9b-4389-92cb-4651fc718991

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology

/-- A continuous negative-supported test vanishes at its cutoff itself.
This remains valid when an intrinsic jump mark equals the cutoff. -/
theorem solution (f : ℝ → ℝ) (ρ : ℝ) (hfcont : Continuous f)
    (hf : ∀ z : ℝ, -ρ < z → f z = 0) : f (-ρ) = 0 := by
  have hclosed : IsClosed (f ⁻¹' ({0} : Set ℝ)) :=
    isClosed_singleton.preimage hfcont
  have hsubset : Ioi (-ρ) ⊆ f ⁻¹' ({0} : Set ℝ) := by
    intro x hx
    simpa using hf x hx
  have hclosure : closure (Ioi (-ρ)) ⊆ f ⁻¹' ({0} : Set ℝ) :=
    closure_minimal hsubset hclosed
  have hmem : -ρ ∈ closure (Ioi (-ρ)) := by
    rw [closure_Ioi]
    exact le_refl (-ρ)
  simpa only [mem_preimage, mem_singleton_iff] using hclosure hmem
