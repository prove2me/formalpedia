-- Prove2me | solution 1 for Eden.unit_sets_invariant_and_unstable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:53:42.250138+00:00
-- url     : https://prove2.me/submissions/ffe4d8ff-65af-470f-b3d4-5f27f5753a4b

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability
import Theorems.Thm_Eden_firstCircle_unstableRelativeTo
import Theorems.Thm_Eden_secondCircle_unstableRelativeTo
import Theorems.Thm_Eden_torus_unstableRelativeTo
import Theorems.Thm_Eden_unstableRelativeTo_mono
import Theorems.Thm_Eden_evolution_image_stationary_radii

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ)
    {K : Set PhaseSpace} (hK : K = firstCircle 1 ∨ K = secondCircle 1 ∨ K = torus) :
    (∀ t : ℝ, 0 ≤ t → evolution c t '' K = K) ∧
      UnstableRelativeTo c attractor K ∧ UnstableRelativeTo c univ K := by
  have hu : UnstableRelativeTo c attractor K := by
    rcases hK with rfl | rfl | rfl
    · exact firstCircle_unstableRelativeTo c
    · exact secondCircle_unstableRelativeTo c
    · exact torus_unstableRelativeTo c
  refine ⟨?_, hu, unstableRelativeTo_mono c (subset_univ _) hu⟩
  intro t ht
  rcases hK with rfl | rfl | rfl
  · exact evolution_image_stationary_radii c ht (Or.inr rfl) (Or.inl rfl)
  · exact evolution_image_stationary_radii c ht (Or.inl rfl) (Or.inr rfl)
  · exact evolution_image_stationary_radii c ht (Or.inr rfl) (Or.inr rfl)
end Eden
