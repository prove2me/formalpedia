-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.length_quotient_bound_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:59:09.809058+00:00
-- url     : https://prove2.me/submissions/73125d00-4d2b-4aba-8f55-d2a9ad2bdcee

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LengthQuotientLeOfLatticeSandwich
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_length_quot_le_of_pow_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedHeckeModels
open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate
open Formalism.LogVandermondeBounds.product_first_zeroth_parts Module
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {M : Type} [AddCommGroup M] [Module R M]
set_option maxHeartbeats 800000
namespace Formalism.HermitianLattices.RamifiedHeckeModels
theorem _root_.solution (ϖ : R) (hϖ : Irreducible ϖ) (S S0 B : Submodule R M) (U D : M →ₗ[R] M)
    (e : ℕ) (hSB : S0 ≤ B) (hU : B.map U ≤ S) (hD : S.map D ≤ B)
    (hUD : ∀ s ∈ S, U (D s) = ϖ ^ e • s) [Module.Free R S] [Module.Finite R S] :
    Module.length R (S ⧸ (S0.map U).comap S.subtype) ≤
      Module.length R (B ⧸ S0.comap B.subtype) + (e * Module.finrank R S : ℕ) := by
  classical
  set T1 : Submodule R S := (S0.map U).comap S.subtype with hT1
  set T2 : Submodule R S := (B.map U).comap S.subtype with hT2
  have h12 : T1 ≤ T2 := Submodule.comap_mono (Submodule.map_mono hSB)
  set Q : Submodule R (S ⧸ T1) := T2.map T1.mkQ with hQ

  have hsplit : Module.length R (S ⧸ T1) = Module.length R Q + Module.length R ((S ⧸ T1) ⧸ Q) :=
    Module.length_eq_add_of_exact Q.subtype Q.mkQ Q.injective_subtype Q.mkQ_surjective
      (LinearMap.exact_subtype_mkQ Q)
  rw [(Submodule.quotientQuotientEquivQuotient T1 T2 h12).length_eq] at hsplit

  have hlen2 : Module.length R (S ⧸ T2) ≤ (e * Module.finrank R S : ℕ) := by
    apply length_quot_le_of_pow_smul ϖ hϖ S T2 e
    intro x
    rw [hT2, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
    exact ⟨D x, hD (Submodule.mem_map_of_mem x.2), hUD x x.2⟩

  have hlen1 : Module.length R Q ≤ Module.length R (B ⧸ S0.comap B.subtype) := by
    let uB : B →ₗ[R] S := (U.domRestrict B).codRestrict S (fun b => hU (Submodule.mem_map_of_mem b.2))
    have huB : ∀ b : B, uB b ∈ T2 := fun b => by
      rw [hT2, Submodule.mem_comap]
      exact ⟨b, b.2, rfl⟩
    let ψ : B →ₗ[R] Q := (T1.mkQ ∘ₗ uB).codRestrict Q (fun b => Submodule.mem_map_of_mem (huB b))
    have hψ : Function.Surjective ψ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      rw [hT2, Submodule.mem_comap] at hx
      obtain ⟨b, hb, hbx⟩ := Submodule.mem_map.1 hx
      refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
      show T1.mkQ (uB ⟨b, hb⟩) = T1.mkQ x
      congr 1
      exact Subtype.ext hbx
    have hker : S0.comap B.subtype ≤ LinearMap.ker ψ := by
      intro b hb
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      show T1.mkQ (uB b) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hT1, Submodule.mem_comap]
      exact Submodule.mem_map_of_mem hb
    let φ := (S0.comap B.subtype).liftQ ψ hker
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨b, rfl⟩ := hψ y
      exact ⟨Submodule.Quotient.mk b, rfl⟩
    exact Module.length_le_of_surjective φ hφ
  rw [hsplit]
  exact add_le_add hlen1 hlen2
end Formalism.HermitianLattices.RamifiedHeckeModels
