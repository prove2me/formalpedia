-- Prove2me | solution 1 for GaloisRepAdic.residual_baseChangeAlong_apply_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2ffd21c2-08cb-5c3b-b612-2c07ef67e1aa

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_residual_baseChangeAlong_apply_ne_one

set_option autoImplicit false

namespace GaloisRepAdic
p2m_export "GaloisRepAdic" "baseChangeAlong residual ρ V"
namespace K6Aux
p2m_open "GaloisRepAdic"

theorem residue_eq_of_residue_map_eq {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] (φ : A →+* B) {a c : A}
    (h : IsLocalRing.residue B (φ a) = IsLocalRing.residue B (φ c)) :
    IsLocalRing.residue A a = IsLocalRing.residue A c := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h ⊢
  rw [← map_sub] at h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
  exact fun hu => h (hu.map φ)

end GaloisRepAdic.K6Aux

theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : ρ.residual.ρ σ ≠ 1) :
    (ρ.baseChangeAlong φ hφ).residual.ρ σ ≠ 1 := by
  classical
  letI : Algebra A B := φ.toAlgebra
  let b := Module.Free.chooseBasis A ρ.V
  let M := LinearMap.toMatrix b b (ρ.ρ σ)

  have hA : M.map (IsLocalRing.residue A) ≠ 1 := by
    intro hM
    apply h
    change (ρ.ρ σ).baseChange (IsLocalRing.ResidueField A) = 1
    apply (LinearMap.toMatrix (Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) b)
      (Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) b)).injective
    rw [LinearMap.toMatrix_baseChange, LinearMap.toMatrix_one,
      IsLocalRing.ResidueField.algebraMap_eq]
    exact hM

  intro hB
  apply hA
  have hB' : ((ρ.ρ σ).baseChange B).baseChange (IsLocalRing.ResidueField B) = 1 := hB
  have hmat := congrArg (LinearMap.toMatrix
    (Algebra.TensorProduct.basis (IsLocalRing.ResidueField B) (Algebra.TensorProduct.basis B b))
    (Algebra.TensorProduct.basis (IsLocalRing.ResidueField B) (Algebra.TensorProduct.basis B b)))
    hB'
  rw [LinearMap.toMatrix_baseChange, LinearMap.toMatrix_baseChange, LinearMap.toMatrix_one,
    Matrix.map_map, IsLocalRing.ResidueField.algebraMap_eq] at hmat

  ext i j
  have hij := congrFun (congrFun hmat i) j
  simp only [Matrix.map_apply, Function.comp_apply, Matrix.one_apply] at hij ⊢
  split_ifs at hij ⊢ with hdiag
  · apply GaloisRepAdic.K6Aux.residue_eq_of_residue_map_eq φ (c := 1)
    rw [map_one, map_one]
    exact hij
  · apply GaloisRepAdic.K6Aux.residue_eq_of_residue_map_eq φ (c := 0)
    rw [map_zero, map_zero]
    exact hij

end S_GaloisRepAdic_residual_baseChangeAlong_apply_ne_one
end P2MW
export P2MW.S_GaloisRepAdic_residual_baseChangeAlong_apply_ne_one (solution)
