-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.ms_rkK_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:12.582816+00:00
-- url     : https://prove2.me/submissions/94bd3681-7f75-4485-8fab-73cbf95bca13

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (b : Basis ι K V) {L : Submodule (𝓞 K) V} (hL : L ≠ ⊥) : 0 < rkK L := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨x, hxL, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
  unfold Formalism.HN.rkK
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨x, Submodule.subset_span hxL⟩, ?_⟩
  intro h
  exact hx0 (congrArg Subtype.val h)
end Formalism.BranchingDeterminantCap
