-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.map_conj_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:41.885815+00:00
-- url     : https://prove2.me/submissions/5c7d904d-d3e7-4f64-ae6d-ec21d4011f46

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MapConjOfBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.CovariantRepresentation
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace Formalism.L2.SG.CovariantRepresentation
theorem _root_.solution (R : Subgroup G) (ν : Measure G) (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν)
    (hi : ν.map (fun x => x⁻¹) = ν) {n : G} (hn : n ∈ R) : ν.map (fun x => n⁻¹ * x * n) = ν := by
  have hinv : Measurable (fun x : G => x⁻¹) := measurable_inv
  have hr : ν.map (fun x => x * n) = ν := by
    have e : (fun x : G => x * n) = (fun x => x⁻¹) ∘ ((fun x => n⁻¹ * x) ∘ (fun x => x⁻¹)) := by
      funext x; simp [mul_inv_rev]
    rw [e, ← map_map hinv ((measurable_const_mul _).comp hinv), ← map_map (measurable_const_mul _) hinv, hi,
      hl _ (R.inv_mem hn), hi]
  have e : (fun x : G => n⁻¹ * x * n) = (fun x => x * n) ∘ (fun x => n⁻¹ * x) := rfl
  rw [e, ← map_map (measurable_mul_const n) (measurable_const_mul _), hl _ (R.inv_mem hn), hr]
end Formalism.L2.SG.CovariantRepresentation
