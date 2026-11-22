-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.isWH_algHom_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:10:17.292321+00:00
-- url     : https://prove2.me/submissions/82341ae8-dab6-416c-9d56-56b2dd5f30d4

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {σ τ M : Type*} [AddCommMonoid M]
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (m : σ →₀ ℕ) (c : R) :
    IsWeightedHomogeneous w' (φ (monomial m c)) (Finsupp.weight w m) := by
  have hC : φ (C c) = C c := by
    rw [← MvPolynomial.algebraMap_eq]
    exact φ.commutes c
  rw [monomial_eq, map_mul, hC, Finsupp.prod, map_prod]
  simp only [map_pow]
  have h := (isWeightedHomogeneous_C w' c).mul
    (IsWeightedHomogeneous.prod m.support (fun v => φ (X v) ^ m v) (fun v => m v • w v)
      (fun v _ => (hφ v).pow (m v)))
  rw [zero_add] at h
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact h
end Formalism.GradedWeylDivisibility
