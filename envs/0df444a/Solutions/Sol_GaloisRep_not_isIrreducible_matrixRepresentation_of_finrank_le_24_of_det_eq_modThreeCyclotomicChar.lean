-- Prove2me | solution 1 for GaloisRep.not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/9f5c9a59-2ea6-53cc-a57e-fa7613cd2de4

import Mathlib
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import Definitions.Def_GaloisRep_ComplexConjugation
import Theorems.Thm_Matrix_GeneralLinearGroup_card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three
import Theorems.Thm_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000
set_option linter.unusedVariables false

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

local instance isAlgebraicQbar_s18 : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_s18 : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_s18 : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

scoped instance instNumberFieldIntermediateField_s18 {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K]
    (E : IntermediateField K L) [FiniteDimensional K E] : NumberField E where
  to_finiteDimensional := .trans ℚ K E

namespace QuadExt
open Module in

theorem finrank_rat_eq {M : Type*} [AddCommGroup M] (i₁ i₂ : Module ℚ M) :
    @finrank ℚ M _ _ i₁ = @finrank ℚ M _ _ i₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim i₁ i₂
  rfl
end QuadExt

open Module NumberField
open scoped IntermediateField NumberField MatrixGroups

namespace FLT
namespace Gapsw6W4SmallDegreeImageDescent

theorem gapsw6_w4_det_surjective_on_range
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hdet : Matrix.GeneralLinearGroup.det.comp ρ =
      WeierstrassCurve.modThreeCyclotomicChar) :
    ∀ d : (ZMod 3)ˣ, ∃ h ∈ ρ.range, Matrix.GeneralLinearGroup.det h = d := by
  intro d
  rcases (by decide : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1) d with h1 | hm
  · subst h1
    exact ⟨1, one_mem _, map_one _⟩
  · subst hm
    refine ⟨ρ complexConjugation, MonoidHom.mem_range.mpr ⟨complexConjugation, rfl⟩, ?_⟩
    have h := DFunLike.congr_fun hdet complexConjugation
    rw [MonoidHom.comp_apply] at h
    rw [h, S18.Parity.modThreeCyclotomicChar_complexConjugation]

theorem gapsw6_w4_no_common_eigenline_of_isIrreducible
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hirr : Representation.IsIrreducible (Deformation.matrixRepresentation ρ)) :
    ¬ ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ ∀ h ∈ ρ.range, ∃ c : ZMod 3,
      Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = c • v := by
  rintro ⟨v, hv0, hall⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subrepresentation (Deformation.matrixRepresentation ρ) :=
    { toSubmodule := Submodule.span (ZMod 3) {v}
      apply_mem_toSubmodule := by
        intro σ x hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨c, hc⟩ := hall (ρ σ) (MonoidHom.mem_range.mpr ⟨σ, rfl⟩)
        rw [Deformation.matrixRepresentation_apply, Matrix.mulVecLin_apply,
          Matrix.mulVec_smul, hc]
        exact Submodule.smul_mem _ a
          (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)) }
  rcases hirr.eq_bot_or_eq_top S with hb | ht
  · have hb' : Submodule.span (ZMod 3) {v} = (⊥ : Submodule (ZMod 3) (Fin 2 → ZMod 3)) :=
      congrArg Subrepresentation.toSubmodule hb
    have hvmem := Submodule.mem_span_singleton_self (R := ZMod 3) v
    rw [hb', Submodule.mem_bot] at hvmem
    exact hv0 hvmem
  · have ht' : Submodule.span (ZMod 3) {v} = (⊤ : Submodule (ZMod 3) (Fin 2 → ZMod 3)) :=
      congrArg Subrepresentation.toSubmodule ht
    have h1 : Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) {v}) = 1 :=
      finrank_span_singleton hv0
    rw [ht', finrank_top, Module.finrank_pi, Fintype.card_fin] at h1
    omega

set_option maxHeartbeats 3200000 in

theorem gapsw6_w4_card_range_eq_finrank_of_fixingSubgroup_eq_ker
    {G : Type*} [Group G]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (hfix : F.fixingSubgroup = ρ.ker) :
    Nat.card ↥ρ.range = Module.finrank ℚ ↥F := by
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩

  have hGal' := (InfiniteGalois.normal_iff_isGalois F).mp
    (by rw [hfix]; exact MonoidHom.normal_ker ρ)
  haveI hNormal : Normal ℚ F := by
    have h := hGal'.to_normal
    convert h using 2
    rfl
  haveI : IsScalarTower ℚ F (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic ℚ F := Algebra.IsAlgebraic.of_finite ℚ _
  haveI : IsGalois ℚ F := ⟨⟩

  have hpoint : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : F),
      algebraMap F (AlgebraicClosure ℚ) ((AlgEquiv.restrictNormalHom F τ) x) =
        τ (algebraMap F (AlgebraicClosure ℚ) x) :=
    fun τ x => AlgEquiv.restrictNormal_commutes τ F x

  have hker_iff : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      AlgEquiv.restrictNormalHom F τ = 1 ↔ τ ∈ F.fixingSubgroup := by
    intro τ
    constructor
    · intro h
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hc := hpoint τ ⟨x, hx⟩
      rw [h] at hc
      simpa using hc.symm
    · intro h
      rw [IntermediateField.mem_fixingSubgroup_iff] at h
      refine AlgEquiv.ext fun x => ?_
      refine (algebraMap F (AlgebraicClosure ℚ)).injective ?_
      rw [hpoint τ x]
      have hfixx : τ (algebraMap F (AlgebraicClosure ℚ) x) =
          algebraMap F (AlgebraicClosure ℚ) x := by
        have hxF : (algebraMap F (AlgebraicClosure ℚ) x) ∈ F := by
          simp [IntermediateField.algebraMap_apply]
        simpa [IntermediateField.algebraMap_apply] using h _ hxF
      rw [hfixx]
      simp

  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom F :
        (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (F ≃ₐ[ℚ] F)) :=
    fun g => ⟨g.liftNormal (AlgebraicClosure ℚ), g.restrict_liftNormal (AlgebraicClosure ℚ)⟩

  have hkerEq : (AlgEquiv.restrictNormalHom F :
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (F ≃ₐ[ℚ] F)).ker = ρ.ker := by
    ext τ
    rw [MonoidHom.mem_ker, hker_iff τ, hfix]

  have h1 : Nat.card ↥ρ.range =
      Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ ρ.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv).symm
  have h2 : Nat.card ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸
      (AlgEquiv.restrictNormalHom F :
        (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (F ≃ₐ[ℚ] F)).ker) =
      Nat.card (F ≃ₐ[ℚ] F) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv
  rw [hkerEq] at h2
  have h3 : Nat.card (F ≃ₐ[ℚ] F) = Module.finrank ℚ F :=
    (IsGalois.card_aut_eq_finrank ℚ F).trans (QuadExt.finrank_rat_eq _ _)
  exact (h1.trans h2).trans h3

end FLT.Gapsw6W4SmallDegreeImageDescent

namespace FLT
namespace Gapsw7X2DihedralLevelOneExclusion
open FLT.Gapsw6W4SmallDegreeImageDescent

theorem gapsw7_x2_subgroup_card_two_dichotomy {G : Type*} [Group G] (H : Subgroup G)
    (hcard : Nat.card ↥H = 2) :
    ∃ g : G, g ∈ H ∧ g ≠ 1 ∧ g * g = 1 ∧ ∀ h ∈ H, h = 1 ∨ h = g := by
  obtain ⟨b, hb, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥H)).mp hcard
  have hbb : b * b = 1 := by
    by_contra hbbne
    have h2 : b * b = b := huniq _ hbbne
    have h3 : b * b = b * 1 := by rw [mul_one]; exact h2
    exact hb (mul_left_cancel h3)
  refine ⟨(b : G), b.property, ?_, ?_, ?_⟩
  · intro h1
    exact hb (Subtype.ext (by simpa using h1))
  · simpa using congrArg Subtype.val hbb
  · intro h hh
    by_cases h1 : (⟨h, hh⟩ : ↥H) = 1
    · left
      simpa using congrArg Subtype.val h1
    · right
      exact congrArg Subtype.val (huniq _ h1)

theorem gapsw7_x2_card_two_common_eigenline (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hcard : Nat.card ↥H = 2) :
    ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ ∀ h ∈ H, ∃ c : ZMod 3,
      Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = c • v := by
  obtain ⟨g, hgH, hgne, hgg, hdich⟩ := gapsw7_x2_subgroup_card_two_dichotomy H hcard
  have hMM : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
    simpa using congrArg Units.val hgg
  by_cases hfix : ∀ w : Fin 2 → ZMod 3,
      Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) w = w
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h0
      have h1 := congrFun h0 0
      rw [Pi.zero_apply] at h1
      exact (by decide : (1 : ZMod 3) ≠ 0) h1
    · intro h hh
      rcases hdich h hh with h1 | h1 <;> subst h1
      · exact ⟨1, by rw [Units.val_one, Matrix.one_mulVec, one_smul]⟩
      · exact ⟨1, by rw [hfix, one_smul]⟩
  · obtain ⟨w, hw⟩ := not_forall.mp hfix
    refine ⟨Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) w - w,
      sub_ne_zero.mpr hw, ?_⟩
    intro h hh
    rcases hdich h hh with h1 | h1 <;> subst h1
    · exact ⟨1, by rw [Units.val_one, Matrix.one_mulVec, one_smul]⟩
    · refine ⟨-1, ?_⟩
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec,
        neg_one_smul, neg_sub]

theorem gapsw7_x2_card_range_two_not_irreducible
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hcard : Nat.card ↥ρ.range = 2) :
    ¬ Representation.IsIrreducible (Deformation.matrixRepresentation ρ) := fun hirr =>
  gapsw6_w4_no_common_eigenline_of_isIrreducible ρ hirr
    (gapsw7_x2_card_two_common_eigenline ρ.range hcard)

end FLT.Gapsw7X2DihedralLevelOneExclusion

open FLT.Gapsw6W4SmallDegreeImageDescent FLT.Gapsw7X2DihedralLevelOneExclusion in
theorem solution
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (hfix : F.fixingSubgroup = ρ.ker)
    (h24 : Module.finrank ℚ F ≤ 24)
    (hunr : ∀ (P : Ideal (NumberField.RingOfIntegers F)) [P.IsMaximal],
      (3 : NumberField.RingOfIntegers F) ∉ P → Algebra.IsUnramifiedAt ℤ P)
    (hdet : Matrix.GeneralLinearGroup.det.comp ρ = WeierstrassCurve.modThreeCyclotomicChar) :
    ¬ Representation.IsIrreducible (Deformation.matrixRepresentation ρ) := by
  intro hirr
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

  have hcard := gapsw6_w4_card_range_eq_finrank_of_fixingSubgroup_eq_ker ρ F hfix
  have hle24 : Nat.card ↥ρ.range ≤ 24 := by rw [hcard]; exact h24
  have hdvd : Nat.card ↥ρ.range ∣ 16 :=
    Matrix.GeneralLinearGroup.card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three
      ρ.range (gapsw6_w4_no_common_eigenline_of_isIrreducible ρ hirr)
      (gapsw6_w4_det_surjective_on_range ρ hdet) hle24
  have hle : Module.finrank ℚ ↥F ≤ 2 :=
    NumberField.finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen F hunr
      (by rw [← hcard]; exact hdvd)

  obtain ⟨h₁, hh₁, hd₁⟩ := gapsw6_w4_det_surjective_on_range ρ hdet 1
  obtain ⟨h₂, hh₂, hd₂⟩ := gapsw6_w4_det_surjective_on_range ρ hdet (-1)
  haveI : Nontrivial ↥ρ.range := by
    refine ⟨⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩, ?_⟩⟩
    intro heq
    have hdeq : Matrix.GeneralLinearGroup.det h₁ = Matrix.GeneralLinearGroup.det h₂ := by
      have h := congrArg (fun x : ↥ρ.range => Matrix.GeneralLinearGroup.det x.1) heq
      simpa using h
    rw [hd₁, hd₂] at hdeq
    exact (by decide : ¬ ((1 : (ZMod 3)ˣ) = -1)) hdeq
  haveI : Finite ↥ρ.range :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
  have h1lt : 1 < Nat.card ↥ρ.range := Finite.one_lt_card
  have hcard2 : Nat.card ↥ρ.range = 2 := by omega
  exact gapsw7_x2_card_range_two_not_irreducible ρ hcard2 hirr

end S_GaloisRep_not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar
end P2MW
export P2MW.S_GaloisRep_not_isIrreducible_matrixRepresentation_of_finrank_le_24_of_det_eq_modThreeCyclotomicChar (solution)
