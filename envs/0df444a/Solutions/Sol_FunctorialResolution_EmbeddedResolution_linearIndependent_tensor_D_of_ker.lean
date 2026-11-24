-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.linearIndependent_tensor_D_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:50:09.888386+00:00
-- url     : https://prove2.me/submissions/39de9d44-a7da-4ed2-91e9-4a74de0ee40c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
namespace FunctorialResolution.EmbeddedResolution
private theorem one_tmul_residueField_surjective (A : Type*) [CommRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Surjective (fun x : M => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a x =>
      obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
      refine ⟨a₀ • x, ?_⟩
      have h1 : (a₀ • (1 : IsLocalRing.ResidueField A)) = IsLocalRing.residue A a₀ := by
        rw [Algebra.smul_def, mul_one]; rfl
      show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (a₀ • x) = _
      rw [← TensorProduct.smul_tmul, h1]
  | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (u + v) = _
      rw [TensorProduct.tmul_add]
      rw [show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] u = x from hu,
        show (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] v = y from hv]
private theorem tmul_eq_zero_of_toCotangent_eq_zero (A : Type*) [CommRing A] [IsLocalRing A]
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (x : ↥I)
    (hx : I.toCotangent x = 0) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x
      = (0 : IsLocalRing.ResidueField A ⊗[A] ↥I) := by
  rw [Ideal.toCotangent_eq_zero] at hx
  have key : ∀ t : A, t ∈ I ^ 2 →
      t ∈ I ∧ ∀ ht : t ∈ I, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (⟨t, ht⟩ : ↥I) = 0 := by
    intro t ht
    rw [sq] at ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro a ha b hb
      refine ⟨Ideal.mul_mem_right _ _ ha, ?_⟩
      intro hab
      have h2 : (⟨a * b, hab⟩ : ↥I) = a • (⟨b, hb⟩ : ↥I) := by
        ext
        simp [smul_eq_mul]
      have h3 : a • (1 : IsLocalRing.ResidueField A) = 0 := by
        rw [Algebra.smul_def, mul_one]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hI ha)
      rw [h2, ← TensorProduct.smul_tmul, h3, TensorProduct.zero_tmul]
    · rintro u v ⟨hu, hu2⟩ ⟨hv, hv2⟩
      refine ⟨Ideal.add_mem _ hu hv, ?_⟩
      intro huv
      have h4 : (⟨u + v, huv⟩ : ↥I) = (⟨u, hu⟩ : ↥I) + ⟨v, hv⟩ := rfl
      rw [h4, TensorProduct.tmul_add, hu2, hv2, add_zero]
  exact (key x hx).2 x.2
private theorem dTensor_apply (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A] (x : ↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))) :
    kerToTensorResidueField k A x
      = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A)) := rfl
private theorem mem_ker_sq_of_tmul_D_eq_zero (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    [IsLocalRing A]
    [Algebra k (IsLocalRing.ResidueField A)] [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
    (x : ↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))))
    (hx : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A))
      = (0 : IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A)) :
    (x : A) ∈ (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) ^ 2 := by
  have : Algebra.FormallySmooth k (residueFieldExtension k A).Ring :=
    inferInstanceAs (Algebra.FormallySmooth k A)
  have hs0 : Subsingleton (Algebra.H1Cotangent k (IsLocalRing.ResidueField A)) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hsub : Subsingleton (residueFieldExtension k A).H1Cotangent :=
    (Algebra.Extension.equivH1CotangentOfFormallySmooth (residueFieldExtension k A)).toEquiv.subsingleton
  have hsub2 : Subsingleton ↥(LinearMap.ker (residueFieldExtension k A).cotangentComplex) := hsub
  have hbot : LinearMap.ker (residueFieldExtension k A).cotangentComplex = ⊥ :=
    Submodule.eq_bot_of_subsingleton
  have hx2 : (x : A) ∈ (residueFieldExtension k A).ker := x.2
  have h0 : (residueFieldExtension k A).cotangentComplex
      (Algebra.Extension.Cotangent.mk ⟨(x : A), hx2⟩) = 0 := by
    rw [Algebra.Extension.cotangentComplex_mk]
    exact hx
  have hinj := LinearMap.ker_eq_bot.mp hbot
  have h1 : Algebra.Extension.Cotangent.mk (⟨(x : A), hx2⟩ : (residueFieldExtension k A).ker) = 0 :=
    hinj (by rw [h0, map_zero])
  rw [Algebra.Extension.Cotangent.mk_eq_zero_iff] at h1
  exact h1
private theorem injective_liftBaseChange_dTensor (k A : Type*) [CommRing k] [CommRing A]
    [Algebra k A] [IsLocalRing A] [Algebra k (IsLocalRing.ResidueField A)]
    [IsScalarTower k A (IsLocalRing.ResidueField A)]
    [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] :
    Function.Injective (LinearMap.liftBaseChange (IsLocalRing.ResidueField A)
      (kerToTensorResidueField k A)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨x, rfl⟩ := one_tmul_residueField_surjective A
    (↥(RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))) z
  have h1 : LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (kerToTensorResidueField k A)
      ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] x)
      = (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A)) := by
    rw [LinearMap.liftBaseChange_tmul, one_smul, dTensor_apply]
  have h2 : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (x : A))
      = (0 : IsLocalRing.ResidueField A ⊗[A] KaehlerDifferential k A) := by
    rw [← h1]; exact hz
  have h3 : (x : A) ∈ (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) ^ 2 :=
    mem_ker_sq_of_tmul_D_eq_zero k A x h2
  have hle : RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))
      ≤ IsLocalRing.maximalIdeal A := by
    intro a ha
    have ha' : algebraMap A (IsLocalRing.ResidueField A) a = 0 := ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha'
  refine tmul_eq_zero_of_toCotangent_eq_zero A
    (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) hle x ?_
  rw [Ideal.toCotangent_eq_zero]
  exact h3
section
variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
  [Algebra k (IsLocalRing.ResidueField A)]
  [IsScalarTower k A (IsLocalRing.ResidueField A)]
  [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
  [Algebra k (IsLocalRing.ResidueField A)]
  [IsScalarTower k A (IsLocalRing.ResidueField A)]
  [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
omit [IsNoetherianRing A] [Module.Free A (KaehlerDifferential k A)]
  [Module.Finite A (KaehlerDifferential k A)]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {ι : Type*}
    (m : ι → (RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) : Ideal A))
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))) := by
  classical
  have hT0 : LinearMap.ker (LinearMap.liftBaseChange (IsLocalRing.ResidueField A)
      (kerToTensorResidueField k A)) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (injective_liftBaseChange_dTensor k A)
  have hmain := hm.map' (LinearMap.liftBaseChange (IsLocalRing.ResidueField A)
      (kerToTensorResidueField k A)) hT0
  have heq : (⇑(LinearMap.liftBaseChange (IsLocalRing.ResidueField A) (kerToTensorResidueField k A)) ∘
      fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))
      = fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A))) := by
    funext i
    simp only [Function.comp_apply, LinearMap.liftBaseChange_tmul, one_smul, dTensor_apply]
  rw [heq] at hmain
  exact hmain
end FunctorialResolution.EmbeddedResolution
