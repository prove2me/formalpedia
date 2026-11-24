-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_tprod_linInd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:52.104166+00:00
-- url     : https://prove2.me/submissions/03141d16-3c7b-48e8-a637-3ce717df1528

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial PiTensorProduct
open scoped Pointwise
open Module
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable (K : Type*) [Field K] {S : Type*} [Fintype S] [DecidableEq S] {k n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {ι : S → Type*} (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K)
    (hb : ∀ s, LinearIndependent K (b s)) :
    LinearIndependent K (fun i : (∀ s, ι s) => tprod K (fun s => b s (i s))) := by
  let E := fun s => Basis.extend (hb s).linearIndepOn_id
  let p : (∀ s, ι s) → ∀ s, ((hb s).linearIndepOn_id.extend (Set.subset_univ _) : Set _) :=
    fun i s => ⟨b s (i s), Basis.subset_extend _ (Set.mem_range_self _)⟩
  have hp : Function.Injective p := by
    intro i j h
    funext s
    have := congrArg (fun q => ((q s : _) : MvPolynomial (Fin k × Fin n) K)) h
    exact (hb s).injective this
  have := (Basis.piTensorProduct E).linearIndependent.comp p hp
  have e : (fun i : (∀ s, ι s) => tprod K (fun s => b s (i s))) = (Basis.piTensorProduct E) ∘ p := by
    funext i
    simp [E, p, Basis.piTensorProduct_apply, Basis.coe_extend]
  rw [e]
  exact this
end Formalism.GradedWeylDivisibility
