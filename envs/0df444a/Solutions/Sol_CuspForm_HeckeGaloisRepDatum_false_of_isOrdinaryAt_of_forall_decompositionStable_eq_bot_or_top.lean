-- Prove2me | solution 1 for CuspForm.HeckeGaloisRepDatum.false_of_isOrdinaryAt_of_forall_decompositionStable_eq_bot_or_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/76a85584-b872-5ba6-b4ec-cf690c5278b6

import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_ResidualGaloisRep_charpoly_eq_of_charpoly_frobenius_eq
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_charpoly_residual
import Theorems.Thm_ResidualGaloisRep_charpoly_baseChangeAlong
import Definitions.Def_GaloisRep_ResidualEquiv
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Theorems.Thm_GaloisRepAdic_not_isOrdinaryAt_ofResidualGaloisRep_of_isEquiv_baseChangeAlong
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_HeckeGaloisRepDatum_false_of_isOrdinaryAt_of_forall_decompositionStable_eq_bot_or_top
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow"

open scoped TensorProduct

open Polynomial

namespace CuspForm
p2m_export "CuspForm" "HeckeGaloisRepDatum heckeAlgebra heckeAlgebra.T"
namespace HeckeGaloisRepDatum
p2m_export "CuspForm.HeckeGaloisRepDatum" "residual_absIrr ρ charpoly_frob residue_surjective residue_π"
p2m_open "CuspForm.HeckeGaloisRepDatum CuspForm"

variable {N : ℕ} [NeZero N] {S : Finset ℕ}
  {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
  {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
  [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
  [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

private theorem _root_.CuspForm.HeckeGaloisRepDatum.residueFieldMap_bijective (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T) :
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap 𝒪 T)) := by
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := H.residue_surjective y
  exact ⟨IsLocalRing.residue 𝒪 x, IsLocalRing.ResidueField.map_residue _ _⟩

p2m_export "CuspForm.HeckeGaloisRepDatum" "residueFieldMap_bijective"

theorem _root_.P2MW.S_CuspForm_HeckeGaloisRepDatum_false_of_isOrdinaryAt_of_forall_decompositionStable_eq_bot_or_top.solution
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T) {p : ℕ} (hp : p.Prime)
    (hres : (GaloisRepAdic.ofResidualGaloisRep H.ρ.residual).IsOrdinaryAt p)
    {𝒪' : Type} [CommRing 𝒪'] [IsLocalRing 𝒪']
    (e : IsLocalRing.ResidueField 𝒪 →+* IsLocalRing.ResidueField 𝒪')
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (hχ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ), IsLocalRing.residue 𝒪' (χ t) = e (θ t))
    (ρ : GaloisRepAdic 𝒪')
    (hfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : 𝒪')))
    (hnsl : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ L : Submodule (IsLocalRing.ResidueField 𝒪') ρ.residual.V,
          (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.residual.ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤) :
    False := by

  let ι : IsLocalRing.ResidueField 𝒪 ≃+* IsLocalRing.ResidueField T :=
    RingEquiv.ofBijective _ H.residueFieldMap_bijective
  let ψ : IsLocalRing.ResidueField T →+* IsLocalRing.ResidueField 𝒪' :=
    e.comp ι.symm.toRingHom
  have hψ : ∀ x : IsLocalRing.ResidueField 𝒪,
      ψ (IsLocalRing.ResidueField.map (algebraMap 𝒪 T) x) = e x := fun x => by
    show e (ι.symm (ι x)) = e x
    rw [RingEquiv.symm_apply_apply]

  have key : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly ((H.ρ.residual.baseChangeAlong ψ).ρ σ) =
        LinearMap.charpoly (ρ.residual.ρ σ) := by
    refine ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq
      (fun M _ _ _ => FrobeniusDensity.statement M) _ _ (S ∪ N.primeFactors) ?_
    intro ℓ hℓ hℓS' A τ hA hτ
    have hℓS : ℓ ∉ S := fun h => hℓS' (Finset.mem_union_left _ h)
    have hℓN : ¬ ℓ ∣ N := fun h =>
      hℓS' (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hℓ, h, NeZero.ne N⟩))
    rw [ResidualGaloisRep.charpoly_baseChangeAlong, GaloisRepAdic.charpoly_residual,
      GaloisRepAdic.charpoly_residual, H.charpoly_frob ℓ hℓ hℓN hℓS A hA τ hτ,
      hfrob ℓ hℓ hℓN hℓS A hA τ hτ]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, map_natCast, Polynomial.map_natCast, H.residue_π, hψ, hχ]
  have h₁ : (H.ρ.residual.baseChangeAlong ψ).IsAbsolutelyIrreducible :=
    H.residual_absIrr.baseChangeAlong ψ
  have h₂ : ρ.residual.IsAbsolutelyIrreducible :=
    ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq _ _ h₁ key
  have he : (H.ρ.residual.baseChangeAlong ψ).IsEquiv ρ.residual :=
    ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq _ _ h₁ h₂ key
  exact GaloisRepAdic.not_isOrdinaryAt_ofResidualGaloisRep_of_isEquiv_baseChangeAlong ψ _ _ he hp
    hnsl hres

end CuspForm.HeckeGaloisRepDatum

end S_CuspForm_HeckeGaloisRepDatum_false_of_isOrdinaryAt_of_forall_decompositionStable_eq_bot_or_top
end P2MW
export P2MW.S_CuspForm_HeckeGaloisRepDatum_false_of_isOrdinaryAt_of_forall_decompositionStable_eq_bot_or_top (solution)
