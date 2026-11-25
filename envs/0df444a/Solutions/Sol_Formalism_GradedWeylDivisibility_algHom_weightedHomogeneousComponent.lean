-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.algHom_weightedHomogeneousComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:55:35.598094+00:00
-- url     : https://prove2.me/submissions/7de48e9a-9206-4c43-ac41-d128941dc51c

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_isWH_algHom_monomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
section General
variable {R : Type*} [CommRing R] {σ τ M : Type*} [AddCommMonoid M]
private theorem weightedHomogeneousComponent_self_of_isWH {w : σ → M} {p : MvPolynomial σ R} {m : M}
    (hp : IsWeightedHomogeneous w p m) : weightedHomogeneousComponent w m p = p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h
  · rfl
  · by_contra hd
    exact h (hp (Ne.symm hd))
private theorem weightedHomogeneousComponent_eq_zero_of_isWH_ne {w : σ → M} {p : MvPolynomial σ R} {m μ : M}
    (hne : m ≠ μ) (hp : IsWeightedHomogeneous w p m) : weightedHomogeneousComponent w μ p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with h
  · by_contra hd
    exact hne ((hp hd).symm.trans h)
  · rfl
end General
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {σ τ M : Type*} [AddCommMonoid M]
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (w : σ → M) (w' : τ → M) (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (μ : M)
    (f : MvPolynomial σ R) :
    φ (weightedHomogeneousComponent w μ f) = weightedHomogeneousComponent w' μ (φ f) := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs := isWH_algHom_monomial φ w w' hφ s (coeff s f)
  have hm : IsWeightedHomogeneous w (monomial s (coeff s f)) (Finsupp.weight w s) :=
    isWeightedHomogeneous_monomial w s (coeff s f) rfl
  by_cases h : Finsupp.weight w s = μ
  · subst h
    rw [weightedHomogeneousComponent_self_of_isWH hm, weightedHomogeneousComponent_self_of_isWH hs]
  · rw [weightedHomogeneousComponent_eq_zero_of_isWH_ne h hm, weightedHomogeneousComponent_eq_zero_of_isWH_ne h hs,
      map_zero]
end Formalism.GradedWeylDivisibility
