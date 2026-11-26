-- Prove2me | solution 1 for EdenVerified.attractor_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:14.815626+00:00
-- url     : https://prove2.me/submissions/9bfa7cf6-0929-44d3-bdaa-e0f020e1c4b0

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_attractor_nonempty
import Theorems.Thm_Eden_attractor_uniformlyAttractsBounded
import Theorems.Thm_Eden_evolution_image_attractor
import Theorems.Thm_Eden_exists_global_forward_solution
import Theorems.Thm_Eden_isCompact_attractor


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, ∃ f : ℝ → PhaseSpace, f 0 = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt f (vectorField c (f t)) t) ∧
    attractor.Nonempty ∧ IsCompact attractor ∧
    (∀ t : ℝ, 0 ≤ t → evolution c t '' attractor = attractor) ∧
    (∀ B : Set PhaseSpace, Bornology.IsBounded B → ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ p ∈ B,
        ∃ q ∈ attractor, dist (evolution c t p) q < ε) :=
  ⟨exists_global_forward_solution c, attractor_nonempty, isCompact_attractor,
    fun t ht => evolution_image_attractor c ht,
    attractor_uniformlyAttractsBounded (by linarith)⟩
end EdenVerified
