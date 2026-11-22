-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.card_gal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:09.316198+00:00
-- url     : https://prove2.me/submissions/872fe097-21df-49aa-a0d0-78948987f529

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_bK_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_b_not_rat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
private theorem isIntegral_b : IsIntegral ℚ b := by
  first
  | exact IsIntegral.of_finite ℚ b
  | exact Algebra.IsIntegral.isIntegral b
private theorem aeval_X_sq_add_C_eq_zero_of_sq_eq_neg (hb : b ^ 2 = -(d : L)) :
    Polynomial.aeval b (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) = 0 := by
  first
  | simp [hb]
  | (rw [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hb]; simp)
private theorem minpoly_natDegree_eq_two_of_sq_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) :
    (minpoly ℚ b).natDegree = 2 := by
  have hint : IsIntegral ℚ b := isIntegral_b
  have hmon : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic := by
    first
    | exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    | monicity!
  have hle : (minpoly ℚ b).natDegree ≤ 2 := by
    have h1 := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ b (aeval_X_sq_add_C_eq_zero_of_sq_eq_neg hb)) hmon.ne_zero
    first
    | rwa [Polynomial.natDegree_X_pow_add_C] at h1
    | exact h1.trans (by compute_degree)
  have hne1 : (minpoly ℚ b).natDegree ≠ 1 := by
    intro h1
    first
    | (rw [minpoly.natDegree_eq_one_iff] at h1; obtain ⟨q, hq⟩ := h1; exact b_not_rat hd hb (IntermediateField.mem_bot.mpr ⟨q, hq⟩))
    | (have h2 : Module.finrank ℚ ℚ⟮b⟯ = 1 := by rw [IntermediateField.adjoin.finrank hint, h1]
       exact b_not_rat hd hb (IntermediateField.adjoin_simple_eq_bot_iff.mp (IntermediateField.finrank_eq_one_iff.mp h2)))
  have hpos := minpoly.natDegree_pos hint
  omega
private theorem Kd_algEquiv_ext_of_apply_bK_eq (σ τ : Kd b ≃ₐ[ℚ] Kd b) (h : σ (bK b) = τ (bK b)) : σ = τ := by
  have hint : IsIntegral ℚ b := isIntegral_b
  have key : (σ : Kd b →ₐ[ℚ] Kd b) = (τ : Kd b →ₐ[ℚ] Kd b) := by
    apply (IntermediateField.adjoin.powerBasis hint).algHom_ext
    first
    | exact h
    | (rw [IntermediateField.adjoin.powerBasis_gen]; exact h)
    | (simp only [IntermediateField.adjoin.powerBasis_gen, AlgEquiv.coe_algHom]; exact h)
  exact AlgEquiv.ext fun x => AlgHom.congr_fun key x
private theorem Kd_algEquiv_bK_eq_or_eq_neg (hb : b ^ 2 = -(d : L)) (σ : Kd b ≃ₐ[ℚ] Kd b) :
    σ (bK b) = bK b ∨ σ (bK b) = -bK b := by
  have h1 : σ (bK b) ^ 2 = bK b ^ 2 := by
    first
    | rw [← map_pow, bK_sq hb, map_neg, map_natCast]
    | (rw [← map_pow, bK_sq hb]; simp)
  have h2 : (σ (bK b) - bK b) * (σ (bK b) + bK b) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · left
    linear_combination h
  · right
    linear_combination h
private theorem minpoly_eq_X_sq_add_C_of_sq_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) :
    minpoly ℚ b = Polynomial.X ^ 2 + Polynomial.C (d : ℚ) := by
  have hint : IsIntegral ℚ b := isIntegral_b
  have hmon : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic := by
    first
    | exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    | monicity!
  obtain ⟨r, hr⟩ := minpoly.dvd ℚ b (aeval_X_sq_add_C_eq_zero_of_sq_eq_neg hb)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact hmon.ne_zero hr
  have hdeg := congrArg Polynomial.natDegree hr
  rw [(minpoly.monic hint).natDegree_mul' hr0, Polynomial.natDegree_X_pow_add_C,
    minpoly_natDegree_eq_two_of_sq_eq_neg hd hb] at hdeg
  have hrm : r.Monic := (minpoly.monic hint).of_mul_monic_left (hr ▸ hmon)
  have hr0d : r.natDegree = 0 := by omega
  have hr1 : r = 1 := by
    first
    | exact (Polynomial.Monic.natDegree_eq_zero hrm).mp hr0d
    | exact Polynomial.eq_one_of_monic_natDegree_zero hrm hr0d
    | (rw [Polynomial.eq_C_of_natDegree_eq_zero hr0d]; have h5 := hrm.leadingCoeff; rw [Polynomial.leadingCoeff, hr0d] at h5; rw [h5, map_one])
  rw [hr, hr1, mul_one]
private theorem Kd_exists_algEquiv_bK_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) :
    ∃ σ : Kd b ≃ₐ[ℚ] Kd b, σ (bK b) = -bK b := by
  have hint : IsIntegral ℚ b := isIntegral_b
  set pb : PowerBasis ℚ (Kd b) := IntermediateField.adjoin.powerBasis hint with hpb
  have hgen : pb.gen = bK b := by
    first
    | rfl
    | (rw [hpb, IntermediateField.adjoin.powerBasis_gen]; rfl)
  have hmin : minpoly ℚ pb.gen = minpoly ℚ b := by
    first
    | exact (minpoly.algebraMap_eq (algebraMap (Kd b) L).injective pb.gen).symm
    | exact IntermediateField.minpoly_eq pb.gen
    | (rw [hpb, IntermediateField.adjoin.powerBasis_gen]; exact IntermediateField.minpoly_gen b)
    | (rw [hpb, IntermediateField.adjoin.powerBasis_gen]; exact IntermediateField.minpoly_gen ℚ b)
  have hroot : Polynomial.aeval (-pb.gen) (minpoly ℚ pb.gen) = 0 := by
    rw [hmin, minpoly_eq_X_sq_add_C_of_sq_eq_neg hd hb, hgen]
    first
    | (simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_natCast]; linear_combination bK_sq hb)
    | (simp; linear_combination bK_sq hb)
    | (simp; rw [neg_sq, bK_sq hb]; ring)
    | (simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]; rw [neg_sq, bK_sq hb]; simp)
  have hbij : Function.Bijective (pb.lift (-pb.gen) hroot) := by
    first
    | exact AlgHom.bijective _
    | exact ⟨(pb.lift (-pb.gen) hroot).toRingHom.injective,
        LinearMap.injective_iff_surjective.mp (pb.lift (-pb.gen) hroot).toRingHom.injective⟩
  refine ⟨AlgEquiv.ofBijective _ hbij, ?_⟩
  have hl : pb.lift (-pb.gen) hroot (bK b) = -bK b := by
    rw [← hgen]
    exact pb.lift_gen _ hroot
  first
  | exact hl
  | (rw [AlgEquiv.ofBijective_apply]; exact hl)
private theorem bK_ne_neg_bK_of_sq_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : bK b ≠ -bK b := by
  intro h
  have h2 : b = -b := by
    first
    | exact congrArg Subtype.val h
    | simpa [bK] using congrArg Subtype.val h
  have h3 : b = 0 := by
    have h4 : (2 : L) * b = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h4 with h5 | h5
    · norm_num at h5
    · exact h5
  rw [h3] at hb
  have h6 : (d : L) = 0 := by linear_combination hb
  have h7 : d = 0 := by exact_mod_cast h6
  omega
end Formalism.FrobeniusOrbits.SplitK
namespace Formalism.FrobeniusOrbits
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
namespace Formalism.FrobeniusOrbits.SplitK
theorem _root_.solution (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : Nat.card (Kd b ≃ₐ[ℚ] Kd b) = 2 := by
  obtain ⟨τ, hτ⟩ := Kd_exists_algEquiv_bK_eq_neg hd hb
  have hne := bK_ne_neg_bK_of_sq_eq_neg hd hb
  let f : (Kd b ≃ₐ[ℚ] Kd b) → ({bK b, -bK b} : Set (Kd b)) := fun σ =>
    ⟨σ (bK b), by rcases Kd_algEquiv_bK_eq_or_eq_neg hb σ with h | h <;> simp [h]⟩
  have hinj : Function.Injective f := fun σ σ' h => Kd_algEquiv_ext_of_apply_bK_eq σ σ' (congrArg Subtype.val h)
  haveI : Finite (Kd b ≃ₐ[ℚ] Kd b) := Finite.of_injective f hinj
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply hne
    rw [h1] at hτ
    first | exact hτ | simpa using hτ
  haveI : Nontrivial (Kd b ≃ₐ[ℚ] Kd b) := ⟨⟨τ, 1, hτ1⟩⟩
  apply le_antisymm
  · calc Nat.card (Kd b ≃ₐ[ℚ] Kd b) ≤ Nat.card ({bK b, -bK b} : Set (Kd b)) :=
          Nat.card_le_card_of_injective f hinj
      _ = 2 := by
        first
        | rw [Nat.card_coe_set_eq, Set.ncard_pair hne]
        | (rw [← Set.ncard_pair hne]; rfl)
        | (rw [← Set.ncard_pair hne, Set.ncard_def]; simp)
        | (rw [← Set.ncard_pair hne]; exact (Set.ncard_eq_toFinset_card' _).symm.trans (by simp))
  · exact Finite.one_lt_card
end Formalism.FrobeniusOrbits.SplitK
