-- Prove2me | solution 1 for Formalism.NG.KernelLengthBounds.length_colData_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:45.281881+00:00
-- url     : https://prove2.me/submissions/de20b629-1e45-4f46-b9b5-dad1f4cffaa7

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockRhoCount
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Theorems.Thm_Formalism_NG_KernelLengthBounds_length_ker_smul_pi
import Theorems.Thm_Formalism_NG_KernelLengthBounds_length_ker_smul_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.NG
namespace KernelLengthBounds
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
private lemma addVal_le_length_quot_span (a : O) :
    IsDiscreteValuationRing.addVal O a ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  by_cases ha : a = 0
  · subst ha
    have htop : Module.length O O = ⊤ := by
      by_contra h
      have hfl : IsFiniteLength O O := Module.length_ne_top_iff.1 h
      have hart : IsArtinianRing O := (isFiniteLength_iff_isNoetherian_isArtinian.1 hfl).2
      apply IsDiscreteValuationRing.not_isField O
      first
        | exact IsArtinianRing.isField_of_isDomain O
        | exact IsArtinianRing.isField_of_domain O
        | exact IsArtinianRing.isField_of_isDomain
    have e : (O ⧸ Ideal.span ({0} : Set O)) ≃ₗ[O] O :=
      Submodule.quotEquivOfEqBot _ (Ideal.span_singleton_eq_bot.mpr rfl)
    rw [e.length_eq, htop]
    exact le_top
  · have hK : algebraMap O (FractionRing O) a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr ha
    let g : O →ₗ[O] KO O := (Submodule.mkQ (1 : Submodule O (FractionRing O))).comp
      (LinearMap.toSpanSingleton O (FractionRing O) (algebraMap O (FractionRing O) a)⁻¹)
    have hg : ∀ x, g x = Submodule.Quotient.mk
        (algebraMap O (FractionRing O) x * (algebraMap O (FractionRing O) a)⁻¹) := by
      intro x
      show Submodule.Quotient.mk (x • (algebraMap O (FractionRing O) a)⁻¹) = _
      rw [Algebra.smul_def]
    have hspan : Ideal.span {a} ≤ LinearMap.ker g := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker, hg,
        Submodule.Quotient.mk_eq_zero, mul_inv_cancel₀ hK]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    have hmem : ∀ x, g x ∈ LinearMap.ker (DistribSMul.toLinearMap O (KO O) a) := by
      intro x
      rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply, hg, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, Algebra.smul_def]
      refine Submodule.mem_one.mpr ⟨x, ?_⟩
      rw [mul_left_comm, mul_inv_cancel₀ hK, mul_one]
    have hsurj : ∀ z ∈ LinearMap.ker (DistribSMul.toLinearMap O (KO O) a), ∃ x, g x = z := by
      intro z hz
      induction z using Submodule.Quotient.induction_on with
      | H k =>
        rw [LinearMap.mem_ker, DistribSMul.toLinearMap_apply, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at hz
        obtain ⟨y, hy⟩ := hz
        refine ⟨y, ?_⟩
        rw [hg, hy, Algebra.smul_def, mul_comm (algebraMap O (FractionRing O) a) k, mul_assoc,
          mul_inv_cancel₀ hK, mul_one]
    have hle : Module.length O (LinearMap.ker (DistribSMul.toLinearMap O (KO O) a)) ≤
        Module.length O (O ⧸ Ideal.span {a}) := by
      refine Module.length_le_of_surjective
        (LinearMap.codRestrict (LinearMap.ker (DistribSMul.toLinearMap O (KO O) a))
          ((Ideal.span {a}).liftQ g hspan) ?_) ?_
      · intro x
        induction x using Submodule.Quotient.induction_on with
        | H x => exact hmem x
      · rintro ⟨z, hz⟩
        obtain ⟨x, hx⟩ := hsurj z hz
        exact ⟨Submodule.Quotient.mk x, Subtype.ext hx⟩
    have h := length_ker_smul_pi (O := O) Unit a
    have e : ↥(LinearMap.ker (DistribSMul.toLinearMap O (Unit → KO O) a)) ≃ₗ[O]
        ↥(LinearMap.ker (DistribSMul.toLinearMap O (KO O) a)) :=
      LinearEquiv.ofSubmodules (LinearEquiv.funUnique Unit O (KO O)) _ _ (by
        ext x
        simp only [Submodule.mem_map_equiv, LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
        constructor
        · intro hx
          simpa using congrFun hx ()
        · intro hx
          funext i
          simpa using hx)
    rw [e.length_eq] at h
    simp only [Fintype.card_unit, Nat.cast_one, one_mul] at h
    rw [← h]
    exact hle
end KernelLengthBounds
end Formalism.NG
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.KernelLengthBounds
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.NG.KernelLengthBounds
theorem _root_.solution (ℓ : ℕ) (δ : O) (e' j : ℕ) (Xw : Type*) [AddCommGroup Xw]
    [Module O Xw] (d : Type) [Fintype d] (h0 : ℕ∞) (hX : Module.length O Xw ≤ h0) :
    Module.length O (ColData O ℓ δ e' j Xw d) ≤
      ((j : ℕ∞) * (Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' : ℕ∞) +
          IsDiscreteValuationRing.addVal O δ) + h0) +
        (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δ := by
  classical
  have hc : Module.length O (LinearMap.ker (DistribSMul.toLinearMap O (KO O) ((ℓ : O) ^ e' * δ))) ≤
      Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' : ℕ∞) + IsDiscreteValuationRing.addVal O δ := by
    refine (length_ker_smul_le _).trans ?_
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul,
      mul_comm (e' : ℕ∞)]
    have := addVal_le_length_quot_span (O := O) (ℓ : O)
    gcongr
  have hd := length_ker_smul_pi (O := O) d δ
  show Module.length O ((Fin j → LinearMap.ker (DistribSMul.toLinearMap O (KO O) ((ℓ : O) ^ e' * δ))) ×
      Xw × LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δ)) ≤ _
  rw [Module.length_prod, Module.length_prod, Module.length_pi_of_fintype, hd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← add_assoc]
  gcongr
end Formalism.NG.KernelLengthBounds
