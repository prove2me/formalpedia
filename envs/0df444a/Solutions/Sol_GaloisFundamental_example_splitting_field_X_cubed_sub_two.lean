-- Prove2me | solution 1 for GaloisFundamental.example_splitting_field_X_cubed_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:15:53.247851+00:00
-- url     : https://prove2.me/submissions/b220788b-4a53-4b58-ae2e-654492e7dac7

import Mathlib

open Polynomial

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

theorem cubeTwo_irr : Irreducible (X ^ 3 - C 2 : ℚ[X]) := by
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_three
  intro b hb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := congrArg (padicValRat 2) hb
  rw [padicValRat.pow] at h
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    have := padicValRat.self (p := 2) (by norm_num)
    simpa using this
  rw [h2] at h
  omega

theorem cubeTwo_bij : Function.Bijective (Gal.galActionHom (X ^ 3 - C 2 : ℚ[X]) ℂ) := by
  have hirr := cubeTwo_irr
  have hdeg : (X ^ 3 - C 2 : ℚ[X]).natDegree = 3 := natDegree_X_pow_sub_C
  have hne : (X ^ 3 - C 2 : ℚ[X]) ≠ 0 := hirr.ne_zero
  have hC : Fintype.card ((X ^ 3 - C 2 : ℚ[X]).rootSet ℂ) = 3 := by
    rw [card_rootSet_eq_natDegree hirr.separable (IsAlgClosed.splits _), hdeg]
  have hR : Fintype.card ((X ^ 3 - C 2 : ℚ[X]).rootSet ℝ) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [mem_rootSet_of_ne hne] at hx hy
    simp only [map_sub, map_pow, aeval_X, aeval_C, eq_ratCast, Rat.cast_ofNat] at hx hy
    have : x ^ 3 = y ^ 3 := by linarith
    exact Subtype.ext ((Odd.pow_inj (by decide : Odd 3)).mp this)
  apply Gal.galActionHom_bijective_of_prime_degree' hirr (by rw [hdeg]; exact Nat.prime_three)
  · omega
  · omega

noncomputable def cubeTwo_equiv : (X ^ 3 - C 2 : ℚ[X]).Gal ≃* Equiv.Perm (Fin 3) :=
  (MulEquiv.ofBijective _ cubeTwo_bij).trans
    (Equiv.permCongrHom (Fintype.equivFinOfCardEq (by
      rw [card_rootSet_eq_natDegree cubeTwo_irr.separable (IsAlgClosed.splits _)]
      exact natDegree_X_pow_sub_C)))

abbrev G3 := Equiv.Perm (Fin 3)

def S3sets : Finset (Finset G3) :=
  (Finset.univ : Finset (Finset G3)).filter
    (fun s => (1 : G3) ∈ s ∧ (∀ a ∈ s, a⁻¹ ∈ s) ∧ ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem S3sets_card : S3sets.card = 6 := by decide +kernel

theorem mem_S3sets (s : Finset G3) : s ∈ S3sets ↔
    ((1 : G3) ∈ s ∧ (∀ a ∈ s, a⁻¹ ∈ s) ∧ ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) := by
  unfold S3sets
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
noncomputable def subgroupEquivS3sets : Subgroup G3 ≃ {s // s ∈ S3sets} where
  toFun H := ⟨Finset.univ.filter (fun g => g ∈ H), by
    rw [mem_S3sets]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨H.one_mem, fun a ha => H.inv_mem ha, fun a ha b hb => H.mul_mem ha hb⟩⟩
  invFun s :=
    { carrier := (s.1 : Set G3)
      mul_mem' := fun {a b} ha hb => ((mem_S3sets s.1).mp s.2).2.2 a ha b hb
      one_mem' := ((mem_S3sets s.1).mp s.2).1
      inv_mem' := fun {a} ha => ((mem_S3sets s.1).mp s.2).2.1 a ha }
  left_inv H := by
    ext g
    simp
  right_inv s := by
    apply Subtype.ext
    ext g
    simp

theorem card_subgroup_S3 : Nat.card (Subgroup (Equiv.Perm (Fin 3))) = 6 := by
  rw [Nat.card_congr subgroupEquivS3sets, Nat.card_eq_fintype_card, Fintype.card_coe, S3sets_card]

theorem card_if_eq {F : Type*} [Field F] (p : F[X]) (hp : p.Separable) :
    Nat.card (IntermediateField F p.SplittingField) = Nat.card (Subgroup p.Gal) := by
  have : IsGalois F p.SplittingField := IsGalois.of_separable_splitting_field hp
  rw [Nat.card_congr IsGalois.intermediateFieldEquivSubgroup.toEquiv,
    Nat.card_congr OrderDual.ofDual]
  rfl

open Polynomial in
theorem solution :
    Module.finrank ℚ (X ^ 3 - C 2 : ℚ[X]).SplittingField = 6 ∧
      Nonempty ((X ^ 3 - C 2 : ℚ[X]).Gal ≃* Equiv.Perm (Fin 3)) ∧
      Nat.card (Subgroup (X ^ 3 - C 2 : ℚ[X]).Gal) = 6 ∧
      Nat.card (IntermediateField ℚ (X ^ 3 - C 2 : ℚ[X]).SplittingField) = 6 := by
  have hsep : (X ^ 3 - C 2 : ℚ[X]).Separable := cubeTwo_irr.separable
  have hsub : Nat.card (Subgroup (X ^ 3 - C 2 : ℚ[X]).Gal) = 6 := by
    rw [Nat.card_congr cubeTwo_equiv.mapSubgroup.toEquiv, card_subgroup_S3]
  refine ⟨?_, ⟨cubeTwo_equiv⟩, hsub, ?_⟩
  · rw [← Gal.card_of_separable hsep, Nat.card_congr cubeTwo_equiv.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  · exact (card_if_eq _ hsep).trans hsub
