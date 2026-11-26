-- Prove2me | solution 1 for EdenVerified.s11_invariant_unstable_sets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:54:29.713935+00:00
-- url     : https://prove2.me/submissions/09d5ab36-dd19-4aef-a721-3932bcbf50c6

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_unit_sets_invariant_and_unstable


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (K : Set PhaseSpace)
    (hK : K = firstCircle 1 ∨ K = secondCircle 1 ∨ K = torus) :
    (∀ t : ℝ, 0 ≤ t → evolution c t '' K = K) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor, Metric.infDist p K < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) K) := by
  have h := unit_sets_invariant_and_unstable c hK
  exact ⟨h.1, h.2.1⟩
end EdenVerified
