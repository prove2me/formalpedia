-- Prove2me | solution 1 for EdenVerified.D11_periodic_union_and_orbits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:03:12.563476+00:00
-- url     : https://prove2.me/submissions/0a9f4112-1e7c-4fe8-ac7e-2328493056be

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_geometricPeriodicOrbits_encard
import Theorems.Thm_Eden_geometricPeriodicOrbits_eq
import Theorems.Thm_Eden_periodicEquilibriumSet_eq_positiveReturnSet
import Theorems.Thm_Eden_positiveReturnSet_subset_attractor


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 0 < c) :
    periodicEquilibriumSet c = attractor ∩
      ({p : PhaseSpace | vectorField c p = 0} ∪
       {p : PhaseSpace | ∃ τ : ℝ, 0 < τ ∧ evolution c τ p = p}) ∧
    periodicEquilibriumSet c =
      {p : PhaseSpace | p ∈ attractor ∧ ∃ τ : ℝ, 0 < τ ∧ evolution c τ p = p} ∧
    geometricPeriodicOrbits c =
      {O : Set PhaseSpace | ∃ p : PhaseSpace,
        (∃ τ : ℝ, 0 < τ ∧ evolution c τ p = p) ∧ vectorField c p ≠ 0 ∧
        {z : PhaseSpace | ∃ τ : ℝ, 0 ≤ τ ∧ evolution c τ p = z} = O} ∧
    geometricPeriodicOrbits c =
      {firstCircle 1, firstCircle 2, secondCircle 1, secondCircle 2} ∧
    (geometricPeriodicOrbits c).encard = 4 := by
  refine ⟨rfl, ?_, rfl, geometricPeriodicOrbits_eq hc, geometricPeriodicOrbits_encard hc⟩
  rw [periodicEquilibriumSet_eq_positiveReturnSet hc]
  ext p
  exact ⟨fun hp => ⟨positiveReturnSet_subset_attractor hc hp, hp⟩, fun hp => hp.2⟩
end EdenVerified
