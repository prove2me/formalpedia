-- Prove2me | solution 1 for CuspForm.HeckeGaloisRepDatum.exists_pi_eq_and_rho_eq_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e931be25-8fc0-53be-a691-81a5dac71402

import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Theorems.Thm_GaloisRepAdic_charpoly_baseChangeAlong
import Theorems.Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_HeckeGaloisRepDatum_exists_pi_eq_and_rho_eq_baseChangeAlong

open scoped TensorProduct
open Polynomial

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "IsIrreducible baseChange baseChangeAlong IsAbsolutelyIrreducible V ρ Equiv IsEquiv"
p2m_open "ResidualGaloisRep"

variable {k : Type} [Field k]

namespace Equiv p2m_export "ResidualGaloisRep.Equiv" "symm trans baseChangeAlong toLinearEquiv map_apply" end Equiv
namespace Equiv
p2m_open_scoped "ResidualGaloisRep.Equiv" in

private noncomputable def _root_.ResidualGaloisRep.Equiv.baseChange' (k' : Type) [Field k'] [Algebra k k']
    {ρ₁ ρ₂ : ResidualGaloisRep k} (e : Equiv ρ₁ ρ₂) :
    Equiv (ρ₁.baseChange k') (ρ₂.baseChange k') :=
  { toLinearEquiv := e.toLinearEquiv.baseChange k k' ρ₁.V ρ₂.V
    map_apply := fun σ x => by
      show e.toLinearEquiv.baseChange k k' ρ₁.V ρ₂.V ((ρ₁.ρ σ).baseChange k' x) =
        (ρ₂.ρ σ).baseChange k' (e.toLinearEquiv.baseChange k k' ρ₁.V ρ₂.V x)
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b v =>
        rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
          LinearMap.baseChange_tmul, e.map_apply]
      | add x y hx hy => simp only [map_add, hx, hy] }

end Equiv
p2m_export "ResidualGaloisRep" "Equiv.baseChange'"
theorem IsIrreducible.of_equiv' {ρ₁ ρ₂ : ResidualGaloisRep k} (e : Equiv ρ₁ ρ₂)
    (h : ρ₁.IsIrreducible) : ρ₂.IsIrreducible := by
  intro W hW
  have hW' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x ∈ W.comap e.toLinearEquiv.toLinearMap,
        ρ₁.ρ σ x ∈ W.comap e.toLinearEquiv.toLinearMap := by
    intro σ x hx
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
    rw [e.map_apply]
    exact hW σ _ hx
  have hWeq : W = (W.comap e.toLinearEquiv.toLinearMap).map e.toLinearEquiv.toLinearMap :=
    (Submodule.map_comap_eq_of_surjective e.toLinearEquiv.surjective W).symm
  rcases h _ hW' with h0 | h1
  · left
    rw [hWeq, h0, Submodule.map_bot]
  · right
    rw [hWeq, h1, Submodule.map_top, LinearEquiv.range]

namespace IsAbsolutelyIrreducible p2m_export "ResidualGaloisRep.IsAbsolutelyIrreducible" "baseChangeAlong" end IsAbsolutelyIrreducible
p2m_open_scoped "ResidualGaloisRep.IsAbsolutelyIrreducible" in
theorem IsAbsolutelyIrreducible.of_isEquiv' {ρ₁ ρ₂ : ResidualGaloisRep k} (he : ρ₁.IsEquiv ρ₂)
    (h : ρ₁.IsAbsolutelyIrreducible) : ρ₂.IsAbsolutelyIrreducible :=
  IsIrreducible.of_equiv' (he.some.baseChange' (AlgebraicClosure k)) h

end ResidualGaloisRep

namespace GaloisRepAdic
p2m_export "GaloisRepAdic" "baseChangeAlong residual Equiv IsEquiv ρ V charpoly_baseChangeAlong"
p2m_open "GaloisRepAdic"

theorem residual_baseChangeAlong_isEquiv
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) :
    (ρ.baseChangeAlong φ hφ).residual.IsEquiv
      (ρ.residual.baseChangeAlong (haveI := hφ; IsLocalRing.ResidueField.map φ)) := by
  haveI := hφ
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    (IsLocalRing.ResidueField.map φ).toAlgebra
  letI : Module (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := Algebra.toModule
  letI : Algebra A (IsLocalRing.ResidueField B) := ((IsLocalRing.residue B).comp φ).toAlgebra
  letI : Module A (IsLocalRing.ResidueField B) := Algebra.toModule
  haveI : IsScalarTower A (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B) :=
    IsScalarTower.right
  haveI : SMulCommClass (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField B) := Algebra.to_smulCommClass
  haveI : IsScalarTower A B (IsLocalRing.ResidueField B) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange A B (IsLocalRing.ResidueField B)
    (IsLocalRing.ResidueField B) ρ.V
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B) ρ.V
  refine ⟨{ toLinearEquiv := e₁.trans e₂.symm, map_apply := fun σ => ?_ }⟩
  change ∀ x : IsLocalRing.ResidueField B ⊗[B] (B ⊗[A] ρ.V),
    (e₁.trans e₂.symm) (((ρ.ρ σ).baseChange B).baseChange (IsLocalRing.ResidueField B) x) =
    ((ρ.ρ σ).baseChange (IsLocalRing.ResidueField A)).baseChange (IsLocalRing.ResidueField B)
      ((e₁.trans e₂.symm) x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul b v =>
      simp only [LinearEquiv.trans_apply, LinearMap.baseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, e₁, e₂]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

end GaloisRepAdic

theorem solution
    {N : ℕ} [NeZero N] {S : Finset ℕ}
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
    {T₀ : Type} [CommRing T₀] [IsLocalRing T₀] [IsNoetherianRing T₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal T₀) T₀] [Algebra 𝒪 T₀] [IsLocalHom (algebraMap 𝒪 T₀)]
    [Module.Finite 𝒪 T₀] [Module.Free 𝒪 T₀]
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H₀ : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T₀)
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T)
    (φ : T₀ →ₐ[𝒪] T) (hφ : IsLocalHom φ.toRingHom) (hfac : ∀ t, φ (H₀.π t) = H.π t) :
    ∃ H' : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T, H'.π = H.π ∧
      H'.ρ = H₀.ρ.baseChangeAlong φ.toRingHom hφ := by
  refine ⟨{ π := H.π
            residue_π := H.residue_π
            adjoin_range_π := H.adjoin_range_π
            exists_point := H.exists_point
            residue_surjective := H.residue_surjective
            ρ := H₀.ρ.baseChangeAlong φ.toRingHom hφ
            charpoly_frob := ?_
            residual_absIrr := ?_ }, rfl, rfl⟩
  · intro ℓ hℓ hℓN hℓS A hA σ hσ
    rw [GaloisRepAdic.charpoly_baseChangeAlong, H₀.charpoly_frob ℓ hℓ hℓN hℓS A hA σ hσ]
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, map_natCast, Polynomial.map_natCast]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hfac]
  · haveI := hφ
    exact ResidualGaloisRep.IsAbsolutelyIrreducible.of_isEquiv'
      ⟨(GaloisRepAdic.residual_baseChangeAlong_isEquiv φ.toRingHom hφ H₀.ρ).some.symm⟩
      (H₀.residual_absIrr.baseChangeAlong _)

end S_CuspForm_HeckeGaloisRepDatum_exists_pi_eq_and_rho_eq_baseChangeAlong
end P2MW
export P2MW.S_CuspForm_HeckeGaloisRepDatum_exists_pi_eq_and_rho_eq_baseChangeAlong (solution)
