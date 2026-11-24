-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.supportVolumeIndex_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:29.170536+00:00
-- url     : https://prove2.me/submissions/5df9bc26-3ea6-4a3a-a21a-4e1c77a5c804

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : SupportVolumeIndex := by
  intro q _ n n'
  have gen : ∀ (A B : Type) [AddCommGroup A] [Module (ZMod q) A] [AddCommGroup B] [Module (ZMod q) B]
      (φ : A →ₗ[ZMod q] B), Function.Surjective φ →
      Nat.card {x : A // φ x = 0} * Nat.card B = Nat.card A := by
    intro A B _ _ _ _ φ hφ
    have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
    have h2 : Nat.card (A ⧸ LinearMap.ker φ) = Nat.card B :=
      Nat.card_congr (φ.quotKerEquivOfSurjective hφ).toEquiv
    have h3 : Nat.card {x : A // φ x = 0} = Nat.card (LinearMap.ker φ) := rfl
    rw [h1, h2, h3]
  have cM : Nat.card (Matrix (Fin n') (Fin n) (ZMod q)) = q ^ (n' * n) := by
    show Nat.card (Fin n' → Fin n → ZMod q) = _
    simp [Nat.card_eq_fintype_card, ZMod.card, ← pow_mul, mul_comm]
  have cV : ∀ k, Nat.card (Fin k → ZMod q) = q ^ k := by
    intro k; simp [Nat.card_eq_fintype_card, ZMod.card]
  constructor
  · intro x0 hx0
    obtain ⟨j0, hj0⟩ : ∃ j, x0 j ≠ 0 := by by_contra h; push Not at h; exact hx0 (funext h)
    let φ : Matrix (Fin n') (Fin n) (ZMod q) →ₗ[ZMod q] (Fin n' → ZMod q) :=
      { toFun := fun x => x.mulVec x0, map_add' := fun x y => Matrix.add_mulVec x y x0,
        map_smul' := fun c x => Matrix.smul_mulVec c x x0 }
    have := gen _ _ φ (by
      intro y
      refine ⟨fun i j => if j = j0 then y i / x0 j0 else 0, ?_⟩
      funext i
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j0 (by intro j _ hj; simp [hj]) (by simp)]
      simp; field_simp)
    rw [cM, cV] at this
    exact this
  · intro fW hfW
    obtain ⟨i0, hi0⟩ : ∃ i, fW i ≠ 0 := by by_contra h; push Not at h; exact hfW (funext h)
    let φ : Matrix (Fin n') (Fin n) (ZMod q) →ₗ[ZMod q] (Fin n → ZMod q) :=
      { toFun := fun x => Matrix.vecMul fW x, map_add' := fun x y => Matrix.vecMul_add x y fW,
        map_smul' := fun c x => Matrix.vecMul_smul fW c x }
    have := gen _ _ φ (by
      intro y
      refine ⟨fun i j => if i = i0 then y j / fW i0 else 0, ?_⟩
      funext j
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMul, dotProduct]
      rw [Finset.sum_eq_single i0 (by intro i _ hi; simp [hi]) (by simp)]
      simp; field_simp)
    rw [cM, cV] at this
    exact this
end Formalism.HermitianLattices.LocalLatticeBases
