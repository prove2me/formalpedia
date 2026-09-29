-- Prove2me | solution 1 for GaloisRep.isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7dd7fb71-6c20-5145-a2ad-3429845b7f10

import Mathlib
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar

namespace S18
namespace Parity

theorem modThreeCyclotomicChar_complexConjugation :
    WeierstrassCurve.modThreeCyclotomicChar complexConjugation = -1 := by
  rw [WeierstrassCurve.modThreeCyclotomicChar_apply]
  have hinj : Function.Injective (complexEmbedding : AlgebraicClosure ℚ → ℂ) :=
    (complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).injective
  have hinv : ∀ t : (AlgebraicClosure ℚ)ˣ, t ∈ rootsOfUnity 3 (AlgebraicClosure ℚ) →
      complexConjugation (t : AlgebraicClosure ℚ) = ((t⁻¹ : (AlgebraicClosure ℚ)ˣ) : _) := by
    intro t ht
    apply hinj
    rw [complexEmbedding_complexConjugation]
    have htC : (Units.map (complexEmbedding : AlgebraicClosure ℚ →* ℂ) t) ∈ rootsOfUnity 3 ℂ := by
      rw [mem_rootsOfUnity] at ht ⊢
      rw [← map_pow, ht, map_one]
    have hnorm : ‖((Units.map (complexEmbedding : AlgebraicClosure ℚ →* ℂ) t : ℂˣ) : ℂ)‖ = 1 :=
      Complex.norm_eq_one_of_mem_rootsOfUnity htC
    calc starRingEnd ℂ (complexEmbedding (t : AlgebraicClosure ℚ))
        = starRingEnd ℂ ((Units.map (complexEmbedding : AlgebraicClosure ℚ →* ℂ) t : ℂˣ) : ℂ) := rfl
      _ = (((Units.map (complexEmbedding : AlgebraicClosure ℚ →* ℂ) t : ℂˣ) : ℂ))⁻¹ :=
          (Complex.inv_eq_conj hnorm).symm
      _ = (((Units.map (complexEmbedding : AlgebraicClosure ℚ →* ℂ) t)⁻¹ : ℂˣ) : ℂ) := by
          rw [← Units.val_inv_eq_inv_val]
      _ = complexEmbedding ((t⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
          rw [← map_inv]; rfl
  have key : (-1 : ZMod 3) = (modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 3)
      (complexConjugation : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) : ZMod 3) := by
    refine modularCyclotomicCharacter.unique _ _ _ fun t ht => ?_
    show complexConjugation (t : AlgebraicClosure ℚ) = _
    rw [hinv t ht]
    have hrw : (t⁻¹ : (AlgebraicClosure ℚ)ˣ) = t ^ (3 - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, (mem_rootsOfUnity 3 t).mp ht]
    rw [hrw, Units.val_pow_eq_pow_val]
    congr 1
  exact Units.ext (by rw [Units.val_neg, Units.val_one]; exact key.symm)

end S18.Parity

theorem solution
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hfix : F.fixingSubgroup ≤ ρ.ker)
    (hdet : Matrix.GeneralLinearGroup.det.comp ρ = WeierstrassCurve.modThreeCyclotomicChar) :
    NumberField.IsTotallyComplex F := by
  classical

  have hχ : WeierstrassCurve.modThreeCyclotomicChar complexConjugation = -1 :=
    S18.Parity.modThreeCyclotomicChar_complexConjugation
  have hρc : ρ complexConjugation ≠ 1 := by
    intro h
    have h2 : Matrix.GeneralLinearGroup.det (ρ complexConjugation) =
        WeierstrassCurve.modThreeCyclotomicChar complexConjugation := by
      rw [← MonoidHom.comp_apply, hdet]
    rw [h, map_one, hχ] at h2
    exact absurd h2 (by decide)
  have hc : complexConjugation ∉ F.fixingSubgroup := fun h => hρc (MonoidHom.mem_ker.mp (hfix h))
  obtain ⟨x, hxF, hx⟩ : ∃ x ∈ F, complexConjugation x ≠ x := by
    by_contra hall
    push Not at hall
    exact hc ((IntermediateField.mem_fixingSubgroup_iff F _).mpr hall)

  let ψ : F →+* ℂ := complexEmbedding.toRingHom.comp (algebraMap F (AlgebraicClosure ℚ))
  have hψ : ¬ NumberField.ComplexEmbedding.IsReal ψ := by
    intro hreal
    rw [NumberField.ComplexEmbedding.isReal_iff] at hreal
    have h1 := RingHom.congr_fun hreal ⟨x, hxF⟩
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq] at h1
    change starRingEnd ℂ (complexEmbedding x) = complexEmbedding x at h1
    rw [← complexEmbedding_complexConjugation] at h1
    exact hx (complexEmbedding.toRingHom.injective h1)

  refine ⟨fun w => ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isReal_iff]
  intro hreal
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ)
    w.embedding ψ (Subsingleton.elim _ _)
  apply hψ
  rw [← hσ]
  exact hreal.comp _

end S_GaloisRep_isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar
end P2MW
export P2MW.S_GaloisRep_isTotallyComplex_of_fixingSubgroup_le_ker_of_det_eq_modThreeCyclotomicChar (solution)
