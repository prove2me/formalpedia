-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.mem_polB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:47:53.285914+00:00
-- url     : https://prove2.me/submissions/5265d357-6b63-43d9-80b9-ba8f93958c09

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace LowHighPartSplit
variable {n : ℕ}
private theorem weight_indicator_eq_degree (d : ℕ × Fin n →₀ ℕ) (j : ℕ) :
    Finsupp.weight (fun x : ℕ × Fin n => if x.1 = j then 1 else 0) d = ∑ a, d (j, a) := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.2) (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x hx _ y hy _ hxy
    rw [Finset.mem_filter] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) hxy
  · intro a _ ha
    exact ⟨(j, a), Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ha, rfl⟩, ha, rfl⟩
  · intro x hx _
    rw [Finset.mem_filter] at hx
    rw [← hx.2]
variable {k : Type*} [Field k] (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
end LowHighPartSplit
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
theorem _root_.solution {R : Type*} [CommRing R] {N : ℕ} {B : ℕ → ℕ} {f : MvPolynomial (ℕ × Fin n) R} :
    f ∈ polB R n N B ↔ ∀ e ∈ f.support, ∀ j, ∑ a, e (j, a) = if j < N then B j else 0 := by
  simp only [polB, Submodule.mem_iInf, mem_weightedHomogeneousSubmodule, IsWeightedHomogeneous]
  constructor
  · intro h e he j
    have := h j (mem_support_iff.mp he)
    rw [weight_indicator_eq_degree] at this
    exact this
  · intro h j d hd
    rw [weight_indicator_eq_degree]
    exact h d (mem_support_iff.mpr hd) j
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
