-- Prove2me | solution 1 for BaconThesis.Multilevel.lemma_12_1_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:45:44.849478+00:00
-- url     : https://prove2.me/submissions/ad88b756-1cbb-4fda-b044-aca149aeb8ca

import Mathlib
import Definitions.Def_BaconThesis_Multilevel_Gmat
import Definitions.Def_BaconThesis_Multilevel_IsDFSubspace

open scoped Matrix

namespace Aux_Bacon_1211
open BaconThesis.Multilevel

lemma sumSigma_apply {N : ℕ} (c : Fin N → Fin N → ℂ) (a b : Fin N) :
    sumSigma c a b = Gmat c a b := by
  unfold sumSigma Gmat
  simp only [Matrix.sum_apply, Matrix.of_apply]
  have e : ∀ i j : Fin N, (if j < i then c i j • (Matrix.single i j 1 + Matrix.single j i 1)
      else 0 : Matrix (Fin N) (Fin N) ℂ) a b
      = (if j < i ∧ i = a ∧ j = b then c i j else 0) + (if j < i ∧ j = a ∧ i = b then c i j else 0) := by
    intro i j
    by_cases h : j < i
    · simp only [h, if_true, true_and, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply,
        smul_eq_mul, mul_add, mul_ite, mul_one, mul_zero]
    · simp only [h, if_false, Matrix.zero_apply, false_and, add_zero]
  simp only [e, Finset.sum_add_distrib]
  have T1 : ∑ i, ∑ j, (if j < i ∧ i = a ∧ j = b then c i j else 0) = if b < a then c a b else 0 := by
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    · intro i _ hi; apply Finset.sum_eq_zero; intro j _; simp [hi]
    · simp
  have T2 : ∑ i, ∑ j, (if j < i ∧ j = a ∧ i = b then c i j else 0) = if a < b then c b a else 0 := by
    rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single a]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    · intro i _ hi; apply Finset.sum_eq_zero; intro j _; simp [hi]
    · simp
  rw [T1, T2]
  by_cases h1 : b < a
  · simp [h1, lt_asymm h1]
  · by_cases h2 : a < b
    · simp [h1, h2]
    · simp [h1, h2]

lemma Gmat_symm {N : ℕ} (g : Fin N → Fin N → ℂ) (a b : Fin N) : Gmat g a b = Gmat g b a := by
  unfold Gmat
  simp only [Matrix.of_apply]
  by_cases h1 : b < a
  · simp [h1, lt_asymm h1]
  · by_cases h2 : a < b
    · simp [h1, h2]
    · simp [h1, h2]

lemma Gmat_diag {N : ℕ} (g : Fin N → Fin N → ℂ) (a : Fin N) : Gmat g a a = 0 := by
  simp [Gmat]

end Aux_Bacon_1211

open BaconThesis.Multilevel Aux_Bacon_1211 in
theorem solution (N : ℕ) (ω : Fin N → ℝ) (hω : Function.Injective ω)
    (g : Fin N → Fin N → ℂ) (hG : ∀ i, ∃ j, Gmat g i j ≠ 0) :
    ¬ ∃ S : Submodule ℂ (Fin N → ℂ), IsDFSubspace g ω S := by
  classical
  rintro ⟨S, hSne, ⟨α₁, α₂, hα⟩, b, h, horth, hdec, hS⟩
  -- eigen-equation for each b l
  have heig : ∀ l i, ((ω i : ℝ) : ℂ) * b l i = ((h l : ℝ) : ℂ) * b l i := by
    intro l i
    have h1 : (Matrix.diagonal fun i => ((ω i : ℝ) : ℂ)) *ᵥ b l = ((h l : ℝ) : ℂ) • b l := by
      rw [hdec, Matrix.sum_mulVec]
      have e : ∀ k, (((h k : ℝ) : ℂ) • Matrix.vecMulVec (b k) (star (b k))) *ᵥ b l
          = if l = k then ((h k : ℝ) : ℂ) • b k else 0 := by
        intro k
        rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, horth, op_smul_eq_smul]
        by_cases hk : k = l
        · subst hk; simp
        · simp [hk, Ne.symm hk]
      rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_ite_eq]
      simp
    have := congrFun h1 i
    simpa [Matrix.mulVec_diagonal] using this
  have hbne : ∀ l, ∃ i, b l i ≠ 0 := by
    intro l
    by_contra hall
    push_neg at hall
    have := horth l l
    rw [if_pos rfl] at this
    have h0 : b l = 0 := funext hall
    rw [h0] at this
    simp at this
  choose π hπ using hbne
  have hsupp : ∀ l i, b l i ≠ 0 → i = π l := by
    intro l i hi
    have e1 := heig l i
    have e2 := heig l (π l)
    have h1 : ((ω i : ℝ) : ℂ) = ((h l : ℝ) : ℂ) := mul_right_cancel₀ hi e1
    have h2 : ((ω (π l) : ℝ) : ℂ) = ((h l : ℝ) : ℂ) := mul_right_cancel₀ (hπ l) e2
    exact hω (Complex.ofReal_injective (h1.trans h2.symm))
  have hdot : ∀ (v : Fin N → ℂ) l, star v ⬝ᵥ b l = star (v (π l)) * b l (π l) := by
    intro v l
    unfold dotProduct
    rw [Finset.sum_eq_single (π l)]
    · rfl
    · intro i _ hi
      have : b l i = 0 := by
        by_contra hne; exact hi (hsupp l i hne)
      simp [this]
    · simp
  have hπinj : Function.Injective π := by
    intro l l' hll'
    by_contra hne
    have := horth l l'
    rw [if_neg hne, hdot, ← hll'] at this
    have h1 : star (b l (π l)) ≠ 0 := star_ne_zero.2 (hπ l)
    exact mul_ne_zero h1 (hll' ▸ hπ l') this
  have hπsurj : Function.Surjective π := Finite.injective_iff_surjective.1 hπinj
  -- a nonzero vector of S
  obtain ⟨ψ, hψS, hψ0⟩ := (Submodule.ne_bot_iff S).1 hSne
  obtain ⟨i, hi⟩ : ∃ i, ψ i ≠ 0 := by
    by_contra hall; push_neg at hall; exact hψ0 (funext hall)
  obtain ⟨l, hl⟩ := hπsurj i
  have hblS : b l ∈ S := by
    rcases hS l with h1 | h1
    · exact h1
    · exfalso
      have := h1 ψ hψS
      rw [hdot, hl] at this
      exact mul_ne_zero (star_ne_zero.2 hi) (hl ▸ hπ l) this
  -- the basis vector e_i lies in S
  have hbl : b l = b l i • Pi.single i 1 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · have : b l j = 0 := by
        by_contra hne; exact hj ((hsupp l j hne).trans hl)
      simp [this, Pi.single_apply, hj]
  have hbi : b l i ≠ 0 := hl ▸ hπ l
  have hei' : (Pi.single i 1 : Fin N → ℂ) = (b l i)⁻¹ • b l := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [inv_mul_cancel₀ hbi]
    · have : b l j = 0 := by
        by_contra hne; exact hj ((hsupp l j hne).trans hl)
      simp [Pi.single_apply, hj, this]
  have hei : (Pi.single i 1 : Fin N → ℂ) ∈ S := by
    rw [hei']; exact S.smul_mem _ hblS
  have heq := (hα _ hei).1
  -- column i of Gmat g vanishes
  have hcol : ∀ j, Gmat g j i = 0 := by
    intro j
    have := congrFun heq j
    rw [Matrix.mulVec_single_one] at this
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [sumSigma_apply] at this
    by_cases hj : j = i
    · subst hj; exact Gmat_diag g j
    · rw [this]; simp [Pi.single_apply, hj]
  obtain ⟨j, hj⟩ := hG i
  exact hj (by rw [Gmat_symm]; exact hcol j)
