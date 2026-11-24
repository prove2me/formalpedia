-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange.derivIdeal_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:00:18.769069+00:00
-- url     : https://prove2.me/submissions/37d36a72-cf47-4047-ad73-2c0d24a94f52

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealFieldExtension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_DerivIdealBaseChange_partialDeriv_mem_map_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
namespace DerivIdealBaseChange
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
private theorem apply_mem_of_forall_partialDeriv_mem {k : Type*} [CommRing k] {ι : Type*} [Finite ι]
    {S : Type*} [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
    [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (X : Set S) (K : Ideal S)
    (h : ∀ i : ι, ∀ x ∈ X, partialDeriv k ι S i x ∈ K)
    (D : Derivation k S S) {x : S} (hx : x ∈ X) : D x ∈ K := by
  classical
  let N : Submodule S (Derivation k S S) :=
    { carrier := {D : Derivation k S S | ∀ y ∈ X, D y ∈ K}
      add_mem' := by
        intro a b ha hb
        show ∀ y ∈ X, (a + b) y ∈ K
        intro y hy
        have hab : (a + b) y = a y + b y := rfl
        rw [hab]
        exact Ideal.add_mem K (ha y hy) (hb y hy)
      zero_mem' := by
        show ∀ y ∈ X, (0 : Derivation k S S) y ∈ K
        intro y _
        have h0 : (0 : Derivation k S S) y = 0 := rfl
        rw [h0]
        exact Ideal.zero_mem K
      smul_mem' := by
        intro c a ha
        show ∀ y ∈ X, (c • a) y ∈ K
        intro y hy
        have hc : (c • a) y = c * a y := rfl
        rw [hc]
        exact Ideal.mul_mem_left K _ (ha y hy) }
  have hspan : (⊤ : Submodule S (Derivation k S S)) ≤ N := by
    rw [← span_range_partialDeriv k ι S, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  have hDN : D ∈ N := hspan Submodule.mem_top
  exact hDN x hx
section
variable (k : Type*) [CommRing k] (L : Type*) [CommRing L] [Algebra k L]
  (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S' : Type*) [CommRing S'] [Algebra L S'] [Algebra (MvPolynomial ι L) S']
  [IsScalarTower L (MvPolynomial ι L) S'] [Algebra.FormallyEtale (MvPolynomial ι L) S']
  [Algebra k S'] [IsScalarTower k L S']
end
end DerivIdealBaseChange
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (L : Type*) [CommRing L] [Algebra k L]
  (ι : Type*) [DecidableEq ι]
  (S : Type*) [CommRing S] [Algebra k S] [Algebra (MvPolynomial ι k) S]
  [IsScalarTower k (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S]
  (S' : Type*) [CommRing S'] [Algebra L S'] [Algebra (MvPolynomial ι L) S']
  [IsScalarTower L (MvPolynomial ι L) S'] [Algebra.FormallyEtale (MvPolynomial ι L) S']
  [Algebra k S'] [IsScalarTower k L S']
namespace FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange
theorem _root_.solution [Fintype ι] (φ : S →ₐ[k] S')
    (hφ : ∀ i : ι, φ (coord k ι S i) = coord L ι S' i) (J : Ideal S) :
    derivIdeal L (Ideal.map φ J) ≤ Ideal.map φ (derivIdeal k J) := by
  rw [derivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
  intro D g hg
  have key : ∀ i : ι, ∀ y ∈ ((Ideal.map φ J : Ideal S') : Set S'),
      partialDeriv L ι S' i y ∈ Ideal.map φ (derivIdeal k J) := by
    intro i y hy
    exact partialDeriv_mem_map_derivIdeal (k := k) (L := L) (ι := ι) (S := S) (S' := S')
      φ hφ i J (show y ∈ Ideal.map φ J from hy)
  exact apply_mem_of_forall_partialDeriv_mem (ι := ι) ((Ideal.map φ J : Ideal S') : Set S')
    (Ideal.map φ (derivIdeal k J)) key D
    (show g ∈ ((Ideal.map φ J : Ideal S') : Set S') from hg)
end FunctorialResolution.EmbeddedResolution.DerivIdealBaseChange
