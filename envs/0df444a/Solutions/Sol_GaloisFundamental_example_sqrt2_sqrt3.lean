-- Prove2me | solution 1 for GaloisFundamental.example_sqrt2_sqrt3
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T15:12:23.83144+00:00
-- url     : https://prove2.me/submissions/eabc1e0f-97b2-4bc9-8289-7051a9dff6bf

import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Fintype.Powerset
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/- A finite, kernel-checked subgroup count, transported to any Klein four-group. -/
namespace ParentKleinFour

def ClosedSet {G : Type*} [Group G] (s : Finset G) : Prop :=
  1 ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ (∀ a, a ∈ s → a⁻¹ ∈ s)

noncomputable def subgroupEquivClosedSets (G : Type*) [Group G] [Fintype G] :
    Subgroup G ≃ {s : Finset G // ClosedSet s} := by
  classical
  refine
    { toFun := fun H => ⟨Finset.univ.filter (fun x => x ∈ H), ?_⟩
      invFun := fun s =>
        { carrier := {x | x ∈ s.1}
          one_mem' := s.2.1
          mul_mem' := fun ha hb => s.2.2.1 _ ha _ hb
          inv_mem' := fun ha => s.2.2.2 _ ha }
      left_inv := ?_
      right_inv := ?_ }
  · refine ⟨by simp, ?_, ?_⟩
    · intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb ⊢
      exact H.mul_mem ha hb
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact H.inv_mem ha
  · intro H
    ext x
    simp
  · intro s
    apply Subtype.ext
    ext x
    simp

abbrev StandardKleinFour := Multiplicative (ZMod 2 × ZMod 2)

instance : DecidablePred (ClosedSet (G := StandardKleinFour)) := fun s => by
  letI inner (a : StandardKleinFour) : Decidable (∀ b ∈ s, a * b ∈ s) := inferInstance
  letI mulClosed : Decidable (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) :=
    Fintype.decidableForallFintype
  unfold ClosedSet
  infer_instance

lemma standard_subgroup_card : Nat.card (Subgroup StandardKleinFour) = 5 := by
  rw [Nat.card_congr (subgroupEquivClosedSets StandardKleinFour), Nat.card_eq_fintype_card]
  decide

theorem subgroup_card (G : Type*) [Group G] [IsKleinFour G] :
    Nat.card (Subgroup G) = 5 := by
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := G) (G₂ := StandardKleinFour)
  exact (Nat.card_congr e.mapSubgroup.toEquiv).trans standard_subgroup_card

end ParentKleinFour


open Polynomial IntermediateField

namespace GaloisExample

noncomputable section

lemma two_not_square : ¬ IsSquare (2 : ℕ) := by norm_num
lemma three_not_square : ¬ IsSquare (3 : ℕ) := by norm_num
lemma six_not_square : ¬ IsSquare (6 : ℕ) := by
  rintro ⟨k, hk⟩
  have hklo : 2 < k := by nlinarith
  nlinarith

lemma no_rat_square {n : ℕ} (hn : ¬ IsSquare n) (q : ℚ) : q ^ 2 ≠ n := by
  intro h
  apply hn
  apply Rat.isSquare_natCast_iff.mp
  exact ⟨q, by simpa [pow_two] using h.symm⟩

lemma sqrt_integral (n : ℕ) : IsIntegral ℚ (Real.sqrt n) := by
  refine ⟨X ^ 2 - C (n : ℚ), monic_X_pow_sub_C _ (by decide), ?_⟩
  simp [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma sqrt_minpoly {n : ℕ} (hn : ¬ IsSquare n) :
    minpoly ℚ (Real.sqrt n) = X ^ 2 - C (n : ℚ) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · exact X_pow_sub_C_irreducible_of_prime (by decide) (no_rat_square hn)
  · simp [Real.sq_sqrt (Nat.cast_nonneg n)]
  · exact monic_X_pow_sub_C _ (by decide)

lemma sqrt_finrank {n : ℕ} (hn : ¬ IsSquare n) :
    Module.finrank ℚ (adjoin ℚ ({Real.sqrt n} : Set ℝ)) = 2 := by
  rw [adjoin.finrank (sqrt_integral n), sqrt_minpoly hn, natDegree_X_pow_sub_C]

lemma sqrt2_representation (x : adjoin ℚ ({Real.sqrt 2} : Set ℝ)) :
    ∃ a b : ℚ, (x : ℝ) = a + b * Real.sqrt 2 := by
  let pb := adjoin.powerBasis (sqrt_integral 2)
  obtain ⟨p, hp, heq⟩ := pb.exists_eq_aeval x
  have hd : pb.dim = 2 := by
    change (minpoly ℚ (Real.sqrt (2 : ℕ))).natDegree = 2
    rw [sqrt_minpoly two_not_square, natDegree_X_pow_sub_C]
  rw [hd] at hp
  refine ⟨p.coeff 0, p.coeff 1, ?_⟩
  rw [p.eq_X_add_C_of_natDegree_le_one (by omega)] at heq
  have h := congrArg (fun y : adjoin ℚ ({Real.sqrt 2} : Set ℝ) => (y : ℝ)) heq
  simpa [pb, add_comm] using h

lemma sqrt3_not_mem_sqrt2 : Real.sqrt 3 ∉ adjoin ℚ ({Real.sqrt 2} : Set ℝ) := by
  intro hmem
  obtain ⟨a, b, hab⟩ := sqrt2_representation ⟨Real.sqrt 3, hmem⟩
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have heq : (a : ℝ) ^ 2 + 2 * (a : ℝ) * b * Real.sqrt 2 + 2 * (b : ℝ) ^ 2 = 3 := by
    nlinarith [congrArg (fun r : ℝ => r ^ 2) hab,
      congrArg (fun r : ℝ => (b : ℝ) ^ 2 * r) hs2]
  have hab0 : a * b = 0 := by
    by_contra h
    have hden : (2 : ℝ) * a * b ≠ 0 := by
      exact_mod_cast (by simpa only [mul_assoc] using
        (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) h) : (2 : ℚ) * a * b ≠ 0)
    apply irrational_sqrt_two
    refine ⟨(3 - a ^ 2 - 2 * b ^ 2) / (2 * a * b), ?_⟩
    push_cast
    apply (div_eq_iff hden).2
    nlinarith [heq]
  rcases mul_eq_zero.mp hab0 with ha | hb
  · have hq : (2 * b) ^ 2 = (6 : ℚ) := by
      apply Rat.cast_injective (α := ℝ)
      push_cast
      simp only [ha, Rat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at heq
      nlinarith [heq]
    exact no_rat_square six_not_square (2 * b) hq
  · have hq : a ^ 2 = (3 : ℚ) := by
      apply Rat.cast_injective (α := ℝ)
      push_cast
      simp only [hb, Rat.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at heq
      simpa using heq
    exact no_rat_square three_not_square a hq

abbrev A := adjoin ℚ ({Real.sqrt 2} : Set ℝ)
abbrev B := adjoin ℚ ({Real.sqrt 3} : Set ℝ)
abbrev K := adjoin ℚ ({Real.sqrt 2, Real.sqrt 3} : Set ℝ)

instance quadratic_A : Algebra.IsQuadraticExtension ℚ A where
  finrank_eq_two' := sqrt_finrank two_not_square

instance quadratic_B : Algebra.IsQuadraticExtension ℚ B where
  finrank_eq_two' := sqrt_finrank three_not_square

lemma K_eq_sup : K = A ⊔ B := by
  rw [K, A, B, ← adjoin_union]
  congr 1

instance finite_K : FiniteDimensional ℚ K := by
  rw [K_eq_sup]
  infer_instance

instance galois_K : IsGalois ℚ K := by
  rw [K_eq_sup]
  have hNA : Normal ℚ A := Algebra.IsQuadraticExtension.normal ℚ A
  have hNB : Normal ℚ B := Algebra.IsQuadraticExtension.normal ℚ B
  exact { to_isSeparable := inferInstance, to_normal := @normal_sup ℚ ℝ _ _ _ A B hNA hNB }

lemma finrank_K : Module.finrank ℚ K = 4 := by
  have hA : Module.finrank ℚ A = 2 := sqrt_finrank two_not_square
  have hB : Module.finrank ℚ B = 2 := sqrt_finrank three_not_square
  have hle : Module.finrank ℚ K ≤ 4 := by
    rw [K_eq_sup]
    simpa only [hA, hB] using finrank_sup_le A B
  have hAK : A ≤ K := by rw [K_eq_sup]; exact le_sup_left
  have hdvd : 2 ∣ Module.finrank ℚ K := by
    simpa [hA] using finrank_dvd_of_le_right hAK
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hne : Module.finrank ℚ K ≠ 2 := by
    intro heq
    have hfields : A = K := eq_of_le_of_finrank_eq hAK (hA.trans heq.symm)
    apply sqrt3_not_mem_sqrt2
    change Real.sqrt 3 ∈ A
    rw [hfields]
    exact subset_adjoin ℚ _ (by simp)
  omega

lemma aut_twice_of_sq_rat (σ : K ≃ₐ[ℚ] K) (x : K) (q : ℚ)
    (hx : x ^ 2 = algebraMap ℚ K q) : σ (σ x) = x := by
  have hs : (σ x) ^ 2 = x ^ 2 := by
    rw [← map_pow, hx, σ.commutes]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
  · rw [h, h]
  · rw [h, map_neg, h, neg_neg]

lemma aut_square (σ : K ≃ₐ[ℚ] K) : σ ^ 2 = 1 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply adjoin_algHom_ext ℚ
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · change σ (σ ⟨Real.sqrt 2, _⟩) = _
    apply aut_twice_of_sq_rat σ _ 2
    apply Subtype.ext
    change Real.sqrt 2 ^ 2 = (2 : ℝ)
    exact Real.sq_sqrt (by norm_num)
  · have hx' : x = Real.sqrt 3 := Set.mem_singleton_iff.mp hx
    subst x
    change σ (σ ⟨Real.sqrt 3, _⟩) = _
    apply aut_twice_of_sq_rat σ _ 3
    apply Subtype.ext
    change Real.sqrt 3 ^ 2 = (3 : ℝ)
    exact Real.sq_sqrt (by norm_num)

instance klein_four_K : IsKleinFour (K ≃ₐ[ℚ] K) where
  card_four := (IsGalois.card_aut_eq_finrank ℚ K).trans finrank_K
  exponent_two := by
    have hcard : Nat.card (K ≃ₐ[ℚ] K) = 4 :=
      (IsGalois.card_aut_eq_finrank ℚ K).trans finrank_K
    have : Nontrivial (K ≃ₐ[ℚ] K) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    apply (Monoid.exponent_eq_prime_iff (by decide : Nat.Prime 2)).mpr
    intro σ hσ
    exact (Nat.dvd_prime (by decide : Nat.Prime 2)).mp
      (orderOf_dvd_of_pow_eq_one (aut_square σ)) |>.resolve_left (by simpa using hσ)

end
end GaloisExample

theorem solution :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ)) = 4 ∧
      IsGalois ℚ (IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ)) ∧
      IsKleinFour (IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ) ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ)) ∧
      Nat.card (Subgroup (IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ) ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ))) = 5 ∧
      Nat.card (IntermediateField ℚ (IntermediateField.adjoin ℚ ({√2, √3} : Set ℝ))) = 5 := by
  refine ⟨GaloisExample.finrank_K, GaloisExample.galois_K,
    GaloisExample.klein_four_K, ParentKleinFour.subgroup_card _, ?_⟩
  exact (Nat.card_congr
    (IsGalois.intermediateFieldEquivSubgroup
      (F := ℚ) (E := GaloisExample.K)).toEquiv).trans
    (ParentKleinFour.subgroup_card (GaloisExample.K ≃ₐ[ℚ] GaloisExample.K))
