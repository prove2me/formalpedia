-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isTaylorExpansionOn_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:06.176811+00:00
-- url     : https://prove2.me/submissions/c304b776-614a-46ed-8beb-f9bd9d3bd5d2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_TaylorExpansion_truncatedSeriesRingHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply



set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k : Type*} [CommRing k] {ι : Type*}
    {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
    [Algebra (MvPolynomial ι k) R] [Algebra A R] [IsLocalRing B] [Algebra ℚ B]
    (φ φ' : R →+* B) (D : Derivation A R R) (β : B)
    (hβ : β ∈ maximalIdeal B)
    (hconst : ∀ c : k,
      φ (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) =
        φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)))
    (hDconst : ∀ c : k, D (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) = 0)
    (hvar : ∀ (i : ι) (N : ℕ), 1 ≤ N →
      TaylorExpansion.truncatedSeries φ D β N (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)) -
          φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.X i)) ∈ maximalIdeal B ^ N) :
    IsTaylorExpansionOn (MvPolynomial ι k) φ φ' D β := by
  intro N hN x
  have hβN : β ^ N ∈ maximalIdeal B ^ N := Ideal.pow_mem_pow hβ N
  have key :
      (TaylorExpansion.truncatedSeriesRingHom φ D β N (maximalIdeal B ^ N) hN hβN).comp
          (algebraMap (MvPolynomial ι k) R) =
        ((Ideal.Quotient.mk (maximalIdeal B ^ N)).comp φ').comp
          (algebraMap (MvPolynomial ι k) R) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have h1 : TaylorExpansion.truncatedSeries φ D β N
            (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c))
          = φ' (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) := by
        rw [TaylorExpansion.truncatedSeries_of_deriv_eq_zero φ D β N hN
          (algebraMap (MvPolynomial ι k) R (MvPolynomial.C c)) (hDconst c)]
        exact hconst c
      simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply, h1]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply]
      exact Ideal.Quotient.eq.2 (hvar i N hN)
  have h := RingHom.congr_fun key x
  simp only [RingHom.coe_comp, Function.comp_apply, TaylorExpansion.truncatedSeriesRingHom_apply] at h
  exact Ideal.Quotient.eq.1 h
end FunctorialResolution.EmbeddedResolution
