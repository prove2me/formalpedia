-- Prove2me | solution 1 for GaloisFundamental.example_real_cube_root_two_not_galois
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:40:53.967225+00:00
-- url     : https://prove2.me/submissions/3da26fe2-1347-4f33-b443-0632c83263c2

import Mathlib

namespace DB51EA49

open Polynomial

lemma cube : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma no_rat_cube : ∀ b : ℚ, b ^ 3 ≠ 2 := by
  intro b hb
  have hr : ((b : ℝ)) ^ 3 = ((2 : ℤ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hb
    simpa using this
  have hirr : Irrational (b : ℝ) := by
    refine irrational_nrt_of_notint_nrt 3 2 hr ?_ (by norm_num)
    rintro ⟨y, hy⟩
    have : (y : ℝ) ^ 3 = 2 := by rw [← hy]; simpa using hr
    have hy3 : y ^ 3 = 2 := by exact_mod_cast this
    have h1 : y ≤ 1 ∨ 2 ≤ y := by omega
    rcases h1 with h1 | h1
    · have : y ^ 3 ≤ 1 := by
        rcases le_or_gt 0 y with h0 | h0
        · have : y ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ h0 h1 3
          simpa using this
        · nlinarith [sq_nonneg y]
      omega
    · have : (2:ℤ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
      norm_num at this
      omega
  exact hirr.ne_rat b rfl

lemma irr : Irreducible (X ^ 3 - C (2 : ℚ)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three no_rat_cube

lemma minpoly_eq : minpoly ℚ ((2 : ℝ) ^ ((1 : ℝ) / 3)) = X ^ 3 - C 2 := by
  symm
  apply minpoly.eq_of_irreducible_of_monic irr
  · rw [map_sub, map_pow, aeval_X, aeval_C, cube, map_ofNat, sub_self]
  · exact monic_X_pow_sub_C _ (by norm_num)

lemma integral : IsIntegral ℚ ((2 : ℝ) ^ ((1 : ℝ) / 3)) := by
  refine ⟨X ^ 3 - C 2, monic_X_pow_sub_C _ (by norm_num), ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, cube, map_ofNat, sub_self]

lemma finrank_eq :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) = 3 := by
  rw [IntermediateField.adjoin.finrank integral, minpoly_eq, natDegree_X_pow_sub_C]

lemma real_cube_unique (y : ℝ) (hy : y ^ 3 = 2) : y = (2 : ℝ) ^ ((1 : ℝ) / 3) := by
  have : y ^ 3 = ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by rw [hy, cube]
  exact (Odd.pow_inj (by decide)).mp this

lemma key (φ : IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ) ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) :
    ((φ ⟨(2 : ℝ) ^ ((1 : ℝ) / 3),
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩ :
        IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) : ℝ) =
      (2 : ℝ) ^ ((1 : ℝ) / 3) := by
  apply real_cube_unique
  have ht : (⟨(2 : ℝ) ^ ((1 : ℝ) / 3),
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩ :
        IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) ^ 3 =
      algebraMap ℚ (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) 2 := by
    apply Subtype.ext
    show ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = algebraMap ℚ ℝ 2
    rw [cube, map_ofNat]
  have h2 := congrArg (fun z => (φ z : ℝ)) ht
  simp only [map_pow, AlgEquiv.commutes] at h2
  refine Eq.trans ?_ (h2.trans ?_)
  · norm_cast
  · exact map_ofNat (algebraMap ℚ ℝ) 2

lemma aut_subsingleton :
    Subsingleton (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ) ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) := by
  constructor
  intro σ τ
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext ℚ
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact Subtype.ext ((key σ).trans (key τ).symm)

end DB51EA49

theorem solution :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) = 3 ∧
      Nat.card (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ) ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) = 1 ∧
      ¬ IsGalois ℚ (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) := by
  have hcard : Nat.card (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ) ≃ₐ[ℚ]
        IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) = 1 := by
    haveI := DB51EA49.aut_subsingleton
    exact Nat.card_unique
  refine ⟨DB51EA49.finrank_eq, hcard, ?_⟩
  intro hG
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ)) :=
    IntermediateField.adjoin.finiteDimensional DB51EA49.integral
  have := IsGalois.card_aut_eq_finrank (F := ℚ)
    (E := IntermediateField.adjoin ℚ ({(2 : ℝ) ^ ((1 : ℝ) / 3)} : Set ℝ))
  rw [hcard, DB51EA49.finrank_eq] at this
  omega
