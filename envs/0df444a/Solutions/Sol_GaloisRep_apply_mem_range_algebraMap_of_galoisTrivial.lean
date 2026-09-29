-- Prove2me | solution 1 for GaloisRep.apply_mem_range_algebraMap_of_galoisTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7e76aff6-cfc9-5b4b-8510-712a0adea036

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_apply_mem_range_algebraMap_of_galoisTrivial

set_option autoImplicit false

theorem solution
    (q : ℕ) [Fact q.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H]
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) ≃ M)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (htriv : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M), σ • m = m)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ)) (x : H) :
    f x ∈ (algebraMap (GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ)).range := by
  classical
  have hq : q.Prime := Fact.out

  have hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ (f x) = f x := by
    intro σ
    let σR : AlgebraicClosure ℚ →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ :=
      { toRingHom := σ.toAlgHom.toRingHom
        commutes' := fun r => σ.commutes (r : ℚ) }
    let g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) :=
      WithConv.toConv (σR.comp (WithConv.ofConv f))
    have hg : e g = e f := by
      rw [he_act σ f g (fun y => rfl), htriv]
    have hgf : g = f := e.injective hg
    have := congrArg (fun z => (WithConv.ofConv z) x) hgf
    exact this

  have hrat : f x ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) := by
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    haveI : Normal ℚ (AlgebraicClosure ℚ) := by
      first
      | infer_instance
      | exact IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
      | exact ⟨fun x => IsAlgClosed.splits _⟩
      | exact ⟨fun x => IsAlgClosed.splits_codomain _⟩
      | exact { toIsAlgebraic := inferInstance, splits' := fun x => IsAlgClosed.splits_codomain _ }
    haveI : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) := by
      first | infer_instance | exact Algebra.IsAlgebraic.isSeparable_of_perfectField
    haveI : IsGalois ℚ (AlgebraicClosure ℚ) := by
      first | infer_instance | exact ⟨⟩ | exact IsGalois.mk
    rw [← InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)),
      IntermediateField.fixingSubgroup_bot]
    exact fun σ => hfix σ
  rw [IntermediateField.mem_bot] at hrat
  obtain ⟨r, hr⟩ := hrat

  haveI := GaloisRep.isFractionRing_ratLocalizedAt q
  haveI : IsDiscreteValuationRing (GaloisRep.ratLocalizedAt q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q hq
  have hint_x : IsIntegral (GaloisRep.ratLocalizedAt q) x := Algebra.IsIntegral.isIntegral x
  have hint_fx : IsIntegral (GaloisRep.ratLocalizedAt q) (f x) := hint_x.map (WithConv.ofConv f)
  have hint_r : IsIntegral (GaloisRep.ratLocalizedAt q) r := by
    rw [← hr] at hint_fx
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (GaloisRep.ratLocalizedAt q) ℚ (AlgebraicClosure ℚ))
      (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mp hint_fx
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := GaloisRep.ratLocalizedAt q) (K := ℚ)).mp hint_r
  refine ⟨y, ?_⟩
  rw [← hr, ← hy]
  rfl

end S_GaloisRep_apply_mem_range_algebraMap_of_galoisTrivial
end P2MW
export P2MW.S_GaloisRep_apply_mem_range_algebraMap_of_galoisTrivial (solution)
