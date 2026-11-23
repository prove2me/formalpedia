-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.pi_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:22.278086+00:00
-- url     : https://prove2.me/submissions/2f9a0a5d-9a0a-41e1-a03a-50d966fd8e2f

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open PrismTransfer
open Formalism.BranchingDeterminantCap.PrismTransfer
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.PrismTransfer
theorem _root_.solution {n : ℕ} (hn : 0 < n) (A : Submodule (𝓞 K) V) (hA : A ≠ ⊥) :
    (Submodule.pi Set.univ fun _ : Fin n => A) ≠ ⊥ := by
  obtain ⟨x, hxA, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  intro h
  have hmem : (Pi.single (⟨0, hn⟩ : Fin n) x : Fin n → V) ∈
      Submodule.pi Set.univ (fun _ : Fin n => A) := by
    rw [Submodule.mem_pi]
    intro i _
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      simpa using hxA
    · simp [Pi.single_apply, hi]
  rw [h, Submodule.mem_bot] at hmem
  exact hx0 (by simpa using congrFun hmem ⟨0, hn⟩)
end Formalism.BranchingDeterminantCap.PrismTransfer
