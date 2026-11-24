-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.formallyEtale_mvPolynomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:11.216503+00:00
-- url     : https://prove2.me/submissions/9c15394d-ca4c-413c-b74d-ce404f7d8b30

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_mapCoeffAlgebra_isScalarTower_of_isScalarTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_mapCoeffAlgebra_isScalarTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply


section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
open MvPolynomial
section
variable (k : Type*) [CommRing k] (ι κ : Type*)
end
section
variable (k : Type*) [CommRing k] (ι κ : Type*)
private theorem iterToSumHom_C_C (a : k) :
    iterToSumRingHom k ι κ (C (C a)) = C a := by
  simp [iterToSumRingHom]
private theorem iterToSumHom_C_X (i : ι) :
    iterToSumRingHom k ι κ (C (X i)) = X (Sum.inl i) := by
  simp [iterToSumRingHom]
private theorem iterToSumHom_X (j : κ) :
    iterToSumRingHom k ι κ (X j) = X (Sum.inr j) := by
  simp [iterToSumRingHom]
private theorem sumEvalIter_C (a : k) :
    sumEvalIter k ι κ (C a) = C (C a) := by
  simp only [sumEvalIter, MvPolynomial.aeval_C]
  rfl
private theorem sumEvalIter_X_inl (i : ι) :
    sumEvalIter k ι κ (X (Sum.inl i)) = C (X i) := by
  simp [sumEvalIter]
private theorem sumEvalIter_X_inr (j : κ) :
    sumEvalIter k ι κ (X (Sum.inr j)) = X j := by
  simp [sumEvalIter]
private theorem iterToSumHom_sumEvalIter (p : MvPolynomial (ι ⊕ κ) k) :
    iterToSumRingHom k ι κ (sumEvalIter k ι κ p) = p := by
  induction p using MvPolynomial.induction_on
  next a => rw [sumEvalIter_C, iterToSumHom_C_C]
  next q r hq hr => simp only [map_add, hq, hr]
  next q v hq =>
    rcases v with i | j
    · simp only [map_mul, hq, sumEvalIter_X_inl, iterToSumHom_C_X]
    · simp only [map_mul, hq, sumEvalIter_X_inr, iterToSumHom_X]
private theorem sumEvalIter_iterToSumHom_C (r : MvPolynomial ι k) :
    sumEvalIter k ι κ (iterToSumRingHom k ι κ (C r)) = C r := by
  induction r using MvPolynomial.induction_on
  next a => rw [iterToSumHom_C_C, sumEvalIter_C]
  next p q hp hq => simp only [map_add, hp, hq]
  next p i hp => simp only [map_mul, hp, iterToSumHom_C_X, sumEvalIter_X_inl]
private theorem sumEvalIter_iterToSumHom (q : MvPolynomial κ (MvPolynomial ι k)) :
    sumEvalIter k ι κ (iterToSumRingHom k ι κ q) = q := by
  induction q using MvPolynomial.induction_on
  next r => exact sumEvalIter_iterToSumHom_C k ι κ r
  next p p' hp hp' => simp only [map_add, hp, hp']
  next p j hp => simp only [map_mul, hp, iterToSumHom_X, sumEvalIter_X_inr]
private theorem bijective_sumEvalIter :
    Function.Bijective (sumEvalIter k ι κ) := by
  constructor
  · exact Function.LeftInverse.injective (iterToSumHom_sumEvalIter k ι κ)
  · exact fun q => ⟨iterToSumRingHom k ι κ q, sumEvalIter_iterToSumHom k ι κ q⟩
attribute [local instance] sumEvalIterAlgebra
private theorem formallyEtale_sumEvalIter :
    Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k)) := by
  have hb : Function.Bijective
      (algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))) :=
    bijective_sumEvalIter k ι κ
  exact Algebra.FormallyEtale.of_equiv
    (AlgEquiv.ofBijective
      (Algebra.ofId (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))) hb)
end
section
variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S]
attribute [local instance] mapCoeffAlgebra
end
section
universe u v
private theorem formallyEtale_mvPolynomial_map (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    [Algebra R A] [Algebra.FormallyEtale R A] (σ : Type*) :
    @Algebra.FormallyEtale (MvPolynomial σ R) (MvPolynomial σ A) _ _
      (RingHom.toAlgebra (MvPolynomial.map (algebraMap R A))) := by
  let : Algebra (MvPolynomial σ R) (MvPolynomial σ A) :=
    RingHom.toAlgebra (MvPolynomial.map (algebraMap R A))
  have : Algebra.FormallyEtale (MvPolynomial σ R)
      (TensorProduct R (MvPolynomial σ R) A) := inferInstance
  have e : TensorProduct R (MvPolynomial σ R) A ≃ₐ[MvPolynomial σ R] MvPolynomial σ A :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm R (MvPolynomial σ R) A).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv R A).toRingEquiv)
      (fun p => by
        have hp : algebraMap (MvPolynomial σ R) (TensorProduct R (MvPolynomial σ R) A) p
            = p ⊗ₜ[R] (1 : A) := rfl
        have hq : algebraMap (MvPolynomial σ R) (MvPolynomial σ A) p
            = MvPolynomial.map (algebraMap R A) p := rfl
        rw [hp, hq]
        simp)
  exact Algebra.FormallyEtale.of_equiv e
end
section
variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S]
attribute [local instance] sumEvalAlgebra
attribute [local instance] sumEvalIterAlgebra
attribute [local instance] mapCoeffAlgebra
variable (T : Type*) [CommRing T]
end
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
open MvPolynomial
variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S]
attribute [local instance] sumEvalAlgebra
attribute [local instance] sumEvalIterAlgebra
attribute [local instance] mapCoeffAlgebra
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S] :
    Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) := by
  have := mapCoeffAlgebra_isScalarTower_of_isScalarTower k ι κ S
  have := mapCoeffAlgebra_isScalarTower k ι κ S
  have h1 : Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k)
      (MvPolynomial κ (MvPolynomial ι k)) := formallyEtale_sumEvalIter k ι κ
  have h2 : Algebra.FormallyEtale (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) :=
    formallyEtale_mvPolynomial_map (MvPolynomial ι k) S κ
  exact Algebra.FormallyEtale.comp (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))
    (MvPolynomial κ S)
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
