-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:31.454735+00:00
-- url     : https://prove2.me/submissions/b6266eae-a1df-435b-8b36-a7d3a8612782

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_isLattice_of_isLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.Idx
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution {M : Submodule O V} (h : IsLat O K M) :
    ∃ (n : ℕ) (β : Basis (Fin n) K V), Submodule.span O (Set.range β) = M := by
  have := isLattice_of_isLat h
  have : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O K V
  obtain ⟨n, c⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := M)
  refine ⟨n, c.extendOfIsLattice K, ?_⟩
  have : Set.range (c.extendOfIsLattice K) = M.subtype '' Set.range c := by
    rw [← Set.range_comp]; congr 1; ext i; simp
  rw [this, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
end Formalism.IrreducibleCountingLemmas.TW.Idx
