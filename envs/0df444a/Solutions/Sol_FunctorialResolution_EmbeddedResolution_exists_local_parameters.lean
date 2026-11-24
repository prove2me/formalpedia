-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_local_parameters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:44.462569+00:00
-- url     : https://prove2.me/submissions/5617be17-a449-4a4b-b2b3-cd7fd6820fa3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_linearIndependent_tensor_D_of_maximalIdeal
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
omit [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution :
    ∃ (h : ℕ) (y : Fin h → A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun i : Fin h =>
          (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (y i))) := by
  classical
  have hfin : Module.Finite A ↥(IsLocalRing.maximalIdeal A) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  have hfin2 : Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)) := inferInstance
  obtain ⟨y, hy⟩ : ∃ y : Fin (Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A))) →
      ↥(IsLocalRing.maximalIdeal A),
      ∀ i, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (y i)
        = Module.finBasis (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)) i := by
    choose y hy using fun i => one_tmul_residueField_surjective A (↥(IsLocalRing.maximalIdeal A))
      (Module.finBasis (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)) i)
    exact ⟨y, hy⟩
  have hspan : Submodule.span A (Set.range y) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis y
      (Module.finBasis (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A)))
      (fun i => hy i)
  refine ⟨_, fun i => ((y i : A)), ?_, ?_⟩
  · have h3 := congrArg (Submodule.map (IsLocalRing.maximalIdeal A).subtype) hspan
    rw [Submodule.map_span, Submodule.map_subtype_top] at h3
    have himg : ((IsLocalRing.maximalIdeal A).subtype '' Set.range y)
        = Set.range (fun i => ((y i : A))) := by
      ext t
      simp
    rw [himg] at h3
    exact h3
  · have hfun : (fun i => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (y i))
        = ⇑(Module.finBasis (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField A ⊗[A] ↥(IsLocalRing.maximalIdeal A))) := funext hy
    refine linearIndependent_tensor_D_of_maximalIdeal k A y ?_
    rw [hfun]
    exact Module.Basis.linearIndependent _
end FunctorialResolution.EmbeddedResolution
