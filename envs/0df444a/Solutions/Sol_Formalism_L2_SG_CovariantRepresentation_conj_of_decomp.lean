-- Prove2me | solution 1 for Formalism.L2.SG.CovariantRepresentation.conj_of_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:59:11.415622+00:00
-- url     : https://prove2.me/submissions/4f7e6cb4-f8fe-4693-92cc-00e7af9d7f97

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IsMulRightInvariantOfLattice
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MapConjOfBounded
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_map_conj_of_mem
import Theorems.Thm_Formalism_L2_SG_CovariantRepresentation_map_conj_of_bounded

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
theorem _root_.solution (R : Subgroup G) (hR : IsClosed (R : Set G)) (ν : Measure G) (_hs : SigmaFinite ν)
    (h0 : ν ≠ 0) (hc : ν (R : Set G)ᶜ = 0) (hK : ∀ K : Set G, IsCompact K → ν K < ⊤)
    (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν) (hi : ν.map (fun x => x⁻¹) = ν) (k n : G)
    (hk : ∀ r, r ∈ R ↔ k⁻¹ * r * k ∈ R) (hn : n ∈ R) (hC : ∃ C : Set G, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C) :
    ν.map (fun x => (k * n)⁻¹ * x * (k * n)) = ν := by
  have e : (fun x : G => (k * n)⁻¹ * x * (k * n)) = (fun x => n⁻¹ * x * n) ∘ (fun x => k⁻¹ * x * k) := by
    funext x
    simp only [Function.comp]
    group
  rw [e, ← map_map ((measurable_const_mul _).mul_const _) ((measurable_const_mul _).mul_const _),
    map_conj_of_bounded R hR ν h0 hc hK hl k hk hC, map_conj_of_mem R ν hl hi hn]
end Formalism.L2.SG.CovariantRepresentation
