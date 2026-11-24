-- Prove2me | solution 1 for BipHamCount.Deterministic.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T02:05:02.429045+00:00
-- url     : https://prove2.me/submissions/c64226a1-0647-4066-a02b-ff2ecbaa61ba

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Core

/-! Ryser, *Combinatorial Mathematics* (1963). The finite signed-cube argument
pairs assignments at a missing column, leaving precisely the bijections. -/

open BipHamCount.Deterministic
open Classical

private def bit {R : Type*} [CommRing R] (b : Bool) : R := if b then 1 else 0
private def sign {R : Type*} [CommRing R] (b : Bool) : R := bit b + bit b - 1

private theorem cube_coeff {R : Type*} [CommRing R] {I J : Type*} [Fintype I] [Fintype J] (f : I → J) :
    (∑ w : J → Bool, (∏ i, sign (R := R) (w i)) * (∏ j, bit (R := R) (w (f j)))) =
    (if Function.Surjective f then 1 else 0) := by
  classical
  by_cases hf : Function.Surjective f
  · rw [if_pos hf, Finset.sum_eq_single (fun _ => true)]
    · simp [sign, bit]
    · intro w _ hw
      have h : ∃ i, w i = false := by
        by_contra! hh
        apply hw
        funext i
        simpa using hh i
      obtain ⟨i, hi⟩ := h
      obtain ⟨j, hj⟩ := hf i
      have hz : (∏ k, bit (R := R) (w (f k))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by simp [bit, hj, hi])
      rw [hz, mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · rw [if_neg hf]
    obtain ⟨i, hi⟩ : ∃ i, ∀ j, f j ≠ i := by simpa [Function.Surjective] using hf
    let flip (w : J → Bool) := Function.update w i (!(w i))
    have he (w : J → Bool) : (∏ j, bit (R := R) (flip w (f j))) =
        ∏ j, bit (R := R) (w (f j)) := by
      apply Finset.prod_congr rfl
      intro j _
      simp [flip, Function.update_of_ne (hi j)]
    have hs (w : J → Bool) : (∏ j, sign (R := R) (flip w j)) =
        -(∏ j, sign (R := R) (w j)) := by
      rw [← Finset.mul_prod_erase _ (fun j => sign (R := R) (flip w j)) (Finset.mem_univ i),
        ← Finset.mul_prod_erase _ (fun j => sign (R := R) (w j)) (Finset.mem_univ i)]
      have other : (∏ j ∈ Finset.univ.erase i, sign (R := R) (flip w j)) =
          ∏ j ∈ Finset.univ.erase i, sign (R := R) (w j) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp [flip, Function.update_of_ne (Finset.mem_erase.mp hj).1]
      rw [other]
      simp [flip, sign, bit]
      cases w i <;> simp
    apply Finset.sum_ninvolution flip
    · intro w
      rw [hs, he]
      ring
    · intro w _ heq
      have h := congrFun heq i
      simp [flip] at h
    · simp
    · intro w
      funext j
      by_cases h : j = i <;> simp [h, flip, Function.update_of_ne]

private theorem ryser {R : Type*} [CommRing R] {I J : Type*} [Fintype I] [Fintype J]
    (hcard : Fintype.card I = Fintype.card J) (x : J → I → R) :
    (∑ w : J → Bool, (∏ i, sign (R := R) (w i)) * ∏ j, ∑ i, x i j * bit (w i)) =
    ∑ σ : I ≃ J, ∏ j, x (σ j) j := by
  classical
  simp_rw [Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  calc
    _ = ∑ f : I → J, (∏ j, x (f j) j) *
        (∑ w : J → Bool, (∏ i, sign (R := R) (w i)) * ∏ j, bit (R := R) (w (f j))) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by
      simp_rw [cube_coeff]
      symm
      apply Fintype.sum_of_injective (fun σ : I ≃ J => (⇑σ : I → J))
        (fun a b h => Equiv.ext (congrFun h))
      · intro f h
        have hn : ¬ Function.Surjective f := by
          intro hf
          exact h ⟨Equiv.ofBijective f ((Fintype.bijective_iff_surjective_and_card _).2 ⟨hf,hcard⟩), rfl⟩
        simp [hn]
      · intro σ
        simp [σ.surjective]

private def characteristic {J : Type*} [Fintype J] [DecidableEq J] : Finset J ≃ (J → Bool) where
  toFun s j := decide (j ∈ s)
  invFun w := Finset.univ.filter fun j => w j
  left_inv s := by ext; simp
  right_inv w := by funext j; simp

private theorem cube_eq_subsets {I J R : Type*} [CommRing R] [Fintype I] [Fintype J] [DecidableEq J]
    (M : Matrix I J R) :
    (∑ w : J → Bool, (∏ j, sign (R := R) (w j)) * ∏ i, ∑ j, M i j * bit (w j)) =
    ∑ X ∈ (Finset.univ : Finset J).powerset,
      (-1 : R) ^ (Fintype.card J - X.card) * ∏ i, ∑ j ∈ X, M i j := by
  classical
  rw [Finset.powerset_univ]
  symm
  apply Fintype.sum_equiv characteristic
  intro X
  have hsign (j : J) : sign (R := R) (characteristic X j) =
      if j ∈ Xᶜ then -1 else 1 := by
    by_cases h : j ∈ X <;> simp [characteristic, sign, bit, h]
  simp_rw [hsign, Fintype.prod_ite_mem, Finset.prod_const, Finset.card_compl]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← Fintype.sum_ite_mem X (fun j => M i j)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j ∈ X <;> simp [bit, characteristic, h]

theorem solution {R I J : Type*} [CommRing R] [Fintype I] [Fintype J]
    [LinearOrder I] [LinearOrder J] (hcard : Fintype.card I = Fintype.card J)
    (M : Matrix I J R) :
    rectPermanent M = ∑ X ∈ (Finset.univ : Finset J).powerset,
      (-1 : R) ^ (Fintype.card J - X.card) * ∏ i, ∑ j ∈ X, M i j := by
  classical
  exact (ryser hcard (fun j i => M i j)).symm.trans (@cube_eq_subsets I J R _ _ _ (Classical.decEq J) M)
