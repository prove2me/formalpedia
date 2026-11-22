-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_isWH_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:03.583203+00:00
-- url     : https://prove2.me/submissions/7a4b3806-8b66-4201-b73f-71f2f6db844a

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace Formalism.BranchingDeterminantCap
private theorem bm_whcSame_lemma {R σ B : Type*} [CommRing R] [AddCommMonoid B] {w : σ → B} {m : B}
    {φ : MvPolynomial σ R} (h : IsWeightedHomogeneous w φ m) : weightedHomogeneousComponent w m φ = φ := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hc
    exact hd (h (Ne.symm hc))
private theorem bm_whcWH_lemma_3 {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (m : B)
    (φ : MvPolynomial σ R) : IsWeightedHomogeneous w (weightedHomogeneousComponent w m φ) m := by
  classical
  intro d hd
  rw [coeff_weightedHomogeneousComponent] at hd
  split_ifs at hd with h
  · exact h
  · exact absurd rfl hd
section bmAList
variable {A : Type*} [Ring A]
end bmAList
section bmACap
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap
section bmACap2
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap2
section bmACap3
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap3
end Formalism.BranchingDeterminantCap
end
end

set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (β : B)
    (x : Module.End R (MvPolynomial σ R))
    (hx : Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) x)
    (F : MvPolynomial σ R) (hF : IsWeightedHomogeneous w F β) : IsWeightedHomogeneous w (x F) β := by
  have h1 : x F = weightedHomogeneousComponent w β (x F) := by
    conv_lhs => rw [← bm_whcSame_lemma hF]
    exact (LinearMap.congr_fun hx.eq F).symm
  rw [h1]
  exact bm_whcWH_lemma_3 w β (x F)
end Formalism.BranchingDeterminantCap
