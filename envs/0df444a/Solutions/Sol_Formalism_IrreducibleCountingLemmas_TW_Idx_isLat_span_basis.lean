-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.isLat_span_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:43.390949+00:00
-- url     : https://prove2.me/submissions/0ada1a38-f5a4-4187-81f8-093ad9a43d9f

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive

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
theorem _root_.solution {d : ℕ} (b : Basis (Fin d) K V) :
    IsLat O K (Submodule.span O (Set.range b)) := by
  refine ⟨Submodule.fg_span (Set.finite_range b), ?_⟩
  rw [Submodule.span_span_of_tower, b.span_eq]
end Formalism.IrreducibleCountingLemmas.TW.Idx
