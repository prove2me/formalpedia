-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.psi_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:30.424292+00:00
-- url     : https://prove2.me/submissions/460abf02-67de-427d-9e64-7f43c8a994ac

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_prod
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_sum_bc
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_col_base
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_col_all
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_pathProductDegrees


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
variable (k : Type) [Field k] {n : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
variable {k isVec S}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
theorem _root_.solution {N i : ℕ} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ} {I : ℤ → Finset (Fin n)}
    (hp : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) (hi : i ≤ N)
    (hS : ∀ j, j ∈ S ↔ j < i) (last : Bool) (m : Fin n)
    (hm : if last then m.val + 1 = n else m.val = 0) :
    WGe isVec S last (sgn last) (gH k isVec S (psiPath k isVec μ N I)) (sgn last * μ i m) := by
  obtain ⟨hfin, -⟩ := pathProductDegrees k n N isVec B μ I hp hI
  have hsub : (Function.mulSupport fun c : ℤ =>
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) k)) N (I c)) ⊆
      ↑(hfin.toFinset ∪ (Finset.Ioc 0 (μ i m) ∪ Finset.Ioc (μ i m) 0)) := by
    intro c hc
    rw [Finset.coe_union]
    exact Or.inl (by simpa using hc)
  unfold psiPath
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, map_prod]
  have := wge_prod (isVec := isVec) (S := S) (last := last) (s := sgn last)
    (hfin.toFinset ∪ (Finset.Ioc 0 (μ i m) ∪ Finset.Ioc (μ i m) 0))
    (fun c => gH k isVec S
      (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) k)) N (I c)))
    (fun c => sgn last * bc c (μ i m))
    (fun c _ => col_all hS c last _ _ (col_base hp hi hS c last m hm) N hi (I c))
  rwa [← Finset.mul_sum, sum_bc _ _ Finset.subset_union_right] at this
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
