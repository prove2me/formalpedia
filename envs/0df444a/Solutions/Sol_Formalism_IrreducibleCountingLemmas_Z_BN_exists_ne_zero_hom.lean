-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.exists_ne_zero_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:50.987778+00:00
-- url     : https://prove2.me/submissions/953229d3-05a3-49ab-b536-e9eede016295

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Lemmata_GeneralBFactSecondVersion_Imports
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Theorems.Thm_Bl_general_b_fact_second_version_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W S : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup S] [Module A S]
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution [FiniteDimensional k W] [IsSemisimpleModule A W] [IsSimpleModule A S]
    (h : ∀ a : A, (∀ w : W, a • w = 0) → ∀ s : S, a • s = 0) : ∃ f : W →ₗ[A] S, f ≠ 0 := by
  exact Bl.general_b_fact_second_version.goal1 (k := k) h
end Formalism.IrreducibleCountingLemmas.Z.BN
