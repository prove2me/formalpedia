-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:53.928004+00:00
-- url     : https://prove2.me/submissions/0d849541-6b65-41f0-8dca-fd06ec7cbf0c

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_exists_smul_mem_of_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open Formalism.LatticeIndexTer.LatticeIndexLength
variable {O K X : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
namespace Formalism.LatticeIndexTer.LatticeIndexLength
theorem _root_.solution (A B : Submodule O X) (hA : A.FG)
    (hB : Submodule.span K (B : Set X) = ⊤) : ∃ d : O, d ≠ 0 ∧ ∀ a ∈ A, d • a ∈ B := by
  classical
  obtain ⟨s, rfl⟩ := hA
  choose f hf0 hf using fun x => exists_smul_mem_of_span (K := K) B hB x
  refine ⟨∏ x ∈ s, f x, Finset.prod_ne_zero_iff.2 (fun x _ => hf0 x), ?_⟩
  intro a ha
  have h : Submodule.span O (s : Set X) ≤ B.comap ((∏ x ∈ s, f x) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.1 hx)
    show ((∏ x ∈ s, f x) • LinearMap.id : X →ₗ[O] X) x ∈ B
    rw [LinearMap.smul_apply, LinearMap.id_apply, hc, mul_comm, mul_smul]
    exact B.smul_mem _ (hf x)
  exact h ha
end Formalism.LatticeIndexTer.LatticeIndexLength
