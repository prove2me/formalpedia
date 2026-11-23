-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.card_ker_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:35.751884+00:00
-- url     : https://prove2.me/submissions/bb87ce91-500e-4eb8-a2ab-9b2342f63604

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_card_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
variable {K : Type*} [Field K]
namespace Formalism.FourierDecayAlt.P.S3x4
theorem _root_.solution [Fintype K] {A B : Type*} (U : Type*) [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup U] [Module K U] [Finite A] [Finite U]
    (R : A →ₗ[K] B) :
    Nat.card {Y : A →ₗ[K] U // LinearMap.ker R ⊓ LinearMap.ker Y = ⊥} =
      Fintype.card K ^ (finrank K U * finrank K (LinearMap.range R)) *
      ∏ j ∈ range (finrank K (LinearMap.ker R)),
        (Fintype.card K ^ finrank K U - Fintype.card K ^ j) := by
  classical
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (LinearMap.ker R)
  have key : ∀ φψ : (LinearMap.ker R →ₗ[K] U) × (W' →ₗ[K] U),
      Function.Injective φψ.1 ↔
        LinearMap.ker R ⊓ LinearMap.ker (LinearMap.ofIsComplProdEquiv hW' φψ) = ⊥ := by
    rintro ⟨φ, ψ⟩
    rw [Submodule.eq_bot_iff, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    constructor
    · rintro h x ⟨hx1, hx2⟩
      have := h ⟨x, hx1⟩ (by
        rw [LinearMap.mem_ker]
        have h3 := LinearMap.mem_ker.mp hx2
        simpa [LinearMap.ofIsComplProdEquiv] using
          (LinearMap.ofIsCompl_apply_left hW' (φ := φ) (ψ := ψ) ⟨x, hx1⟩).symm.trans h3)
      simpa using congrArg Subtype.val this
    · rintro h ⟨x, hx1⟩ hx2
      have := h x ⟨hx1, by
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        have h3 := LinearMap.mem_ker.mp hx2
        exact (LinearMap.ofIsCompl_apply_left hW' (φ := φ) (ψ := ψ) ⟨x, hx1⟩).trans h3⟩
      exact Subtype.ext this
  have e : {Y : A →ₗ[K] U // LinearMap.ker R ⊓ LinearMap.ker Y = ⊥} ≃
      {φ : LinearMap.ker R →ₗ[K] U // Function.Injective φ} × (W' →ₗ[K] U) :=
    (((LinearMap.ofIsComplProdEquiv hW' (F := U)).toEquiv.subtypeEquiv
      (p := fun φψ : (LinearMap.ker R →ₗ[K] U) × (W' →ₗ[K] U) => Function.Injective φψ.1)
      (q := fun Y : A →ₗ[K] U => LinearMap.ker R ⊓ LinearMap.ker Y = ⊥) key).symm).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun φ : LinearMap.ker R →ₗ[K] U => Function.Injective φ))
  have : Finite (W' →ₗ[K] U) := Module.finite_of_finite K
  let _ : Fintype (W' →ₗ[K] U) := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_prod, card_injective, mul_comm]
  congr 1
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), Module.finrank_linearMap]
  have h1 := Submodule.finrank_add_eq_of_isCompl hW'
  have h2 := LinearMap.finrank_range_add_finrank_ker R
  congr 1
  rw [mul_comm]; congr 1; omega
end Formalism.FourierDecayAlt.P.S3x4
