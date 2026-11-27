-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:18.548772+00:00
-- url     : https://prove2.me/submissions/305a195e-a0c8-4283-88d0-e113fb22bff3

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 5:3 (Hestenes–Stiefel 1952, p. 415): (5:6a)–(5:6d), `|rᵢ| ≤ |pᵢ|` with strict
inequality for `0 < i < m`, and acute angles between the nonzero directions; `m` is the step at
which the cg-method terminates (`rₘ = 0`, `rⱼ ≠ 0` for `j < m`). (5:6b) and (5:6d) are stated at
the paper's index `i + 1 > 0`. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i j : ℕ, i ≤ j → (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ j).p =
      ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r) *
        ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) /
        ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r)) ∧
    (∀ i : ℕ, (cgIter A k x₀ (i + 1)).p ⬝ᵥ (cgIter A k x₀ (i + 1)).p =
        (cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r +
          cgBeta A k x₀ i ^ 2 * ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) ∧
      (cgIter A k x₀ (i + 1)).p ⬝ᵥ (cgIter A k x₀ (i + 1)).p =
        ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) ^ 2 *
          ∑ j ∈ Finset.range (i + 2), 1 / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) ∧
    (∀ i j : ℕ, (i + 1 < j ∨ j + 1 < i) →
      (cgIter A k x₀ i).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ j).r) = 0) ∧
    (∀ i : ℕ, (cgIter A k x₀ (i + 1)).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ (i + 1)).r) =
      (cgIter A k x₀ (i + 1)).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ (i + 1)).p) +
        cgBeta A k x₀ i ^ 2 * ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p))) ∧
    (∀ i : ℕ, (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r ≤
      (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) ∧
    (∀ i : ℕ, 0 < i → i < m → (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r <
      (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) ∧
    (∀ i j : ℕ, i < m → j < m → 0 < (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ j).p) := by
      have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
        intro u v
        have hT : Aᵀ = A := by
          have := hA.1
          rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
      have hpos : ∀ w : Fin n → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (A *ᵥ w) := by
        intro w hw
        simpa using hA.dotProduct_mulVec_pos hw
      have hself : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ w := fun w =>
        Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
      have hzero : ∀ w : Fin n → ℝ, w ⬝ᵥ w = 0 → w = 0 := fun w hw => dotProduct_self_eq_zero.mp hw
      suffices key : ∀ (R P : ℕ → (Fin n → ℝ)) (α β : ℕ → ℝ),
          P 0 = R 0 →
          (∀ i, α i = R i ⬝ᵥ R i / (P i ⬝ᵥ (A *ᵥ P i))) →
          (∀ i, β i = R (i+1) ⬝ᵥ R (i+1) / (R i ⬝ᵥ R i)) →
          (∀ i, R (i+1) = R i - α i • (A *ᵥ P i)) →
          (∀ i, P (i+1) = R (i+1) + β i • P i) →
          (∀ j < m, R j ≠ 0) →
        (∀ i j : ℕ, i ≤ j → P i ⬝ᵥ P j = (R j ⬝ᵥ R j) * (P i ⬝ᵥ P i) / (R i ⬝ᵥ R i)) ∧
        (∀ i : ℕ, P (i + 1) ⬝ᵥ P (i + 1) = R (i + 1) ⬝ᵥ R (i + 1) + β i ^ 2 * (P i ⬝ᵥ P i) ∧
          P (i + 1) ⬝ᵥ P (i + 1) = (R (i + 1) ⬝ᵥ R (i + 1)) ^ 2 *
              ∑ j ∈ Finset.range (i + 2), 1 / (R j ⬝ᵥ R j)) ∧
        (∀ i j : ℕ, (i + 1 < j ∨ j + 1 < i) → R i ⬝ᵥ (A *ᵥ R j) = 0) ∧
        (∀ i : ℕ, R (i + 1) ⬝ᵥ (A *ᵥ R (i + 1)) =
          P (i + 1) ⬝ᵥ (A *ᵥ P (i + 1)) + β i ^ 2 * (P i ⬝ᵥ (A *ᵥ P i))) ∧
        (∀ i : ℕ, R i ⬝ᵥ R i ≤ P i ⬝ᵥ P i) ∧
        (∀ i : ℕ, 0 < i → i < m → R i ⬝ᵥ R i < P i ⬝ᵥ P i) ∧
        (∀ i j : ℕ, i < m → j < m → 0 < P i ⬝ᵥ P j) by
        exact key (fun i => (cgIter A k x₀ i).r)
          (fun i => (cgIter A k x₀ i).p) (fun i => cgAlpha A (cgIter A k x₀ i))
          (fun i => cgBeta A k x₀ i)
          rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          hact
      intro R P α β hP0 hα hβ hRs hPs hact
      have hRP0 : ∀ i, R i = 0 → P i = 0 := by
        intro i hi
        cases i with
        | zero => rw [hP0, hi]
        | succ i => rw [hPs, hβ, hi]; simp
      have hαP : ∀ i, α i = 0 → P i = 0 := by
        intro i hi
        rw [hα, div_eq_zero_iff] at hi
        rcases hi with hi | hi
        · exact hRP0 i (hzero _ hi)
        · by_contra hne
          exact (hpos _ hne).ne' hi
      have hQ : ∀ i, (∀ j < i, R i ⬝ᵥ P j = 0 ∧ R i ⬝ᵥ R j = 0 ∧ P i ⬝ᵥ (A *ᵥ P j) = 0) ∧
          R i ⬝ᵥ P i = R i ⬝ᵥ R i := by
        intro i
        induction i with
        | zero => exact ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by rw [hP0]⟩
        | succ i ih =>
          obtain ⟨ih1, ih2⟩ := ih
          have hii : R (i+1) ⬝ᵥ P i = 0 := by
            by_cases hp : P i = 0
            · rw [hp]; simp
            · have hpp := hpos _ hp
              rw [hRs, sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ P i), ih2, hα]
              simp only [smul_eq_mul]
              field_simp
              ring
          have ha : ∀ j < i + 1, R (i+1) ⬝ᵥ P j = 0 := by
            intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
            · rw [hRs, sub_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ P i), ← hsym,
                (ih1 j hj).1, (ih1 j hj).2.2]
              simp
            · rw [hj]; exact hii
          have hb : ∀ j < i + 1, R (i+1) ⬝ᵥ R j = 0 := by
            intro j hj
            cases j with
            | zero => rw [← hP0]; exact ha 0 hj
            | succ j =>
              have e : R (j+1) = P (j+1) - β j • P j := by rw [hPs]; abel
              rw [e, dotProduct_sub, dotProduct_smul, ha _ hj, ha j (by omega)]
              simp
          have hRA' : ∀ j < i, R (i+1) ⬝ᵥ (A *ᵥ P j) = 0 := by
            intro j hj
            by_cases h0 : α j = 0
            · rw [hαP j h0]; simp
            · have e : α j • (A *ᵥ P j) = R j - R (j+1) := by rw [hRs]; abel
              have : α j * (R (i+1) ⬝ᵥ (A *ᵥ P j)) = 0 := by
                rw [← smul_eq_mul, ← dotProduct_smul, e, dotProduct_sub, hb j (by omega),
                  hb (j+1) (by omega)]
                simp
              rcases mul_eq_zero.mp this with h1 | h1
              · exact absurd h1 h0
              · exact h1
          refine ⟨fun j hj => ⟨ha j hj, hb j hj, ?_⟩, ?_⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
            · rw [hPs, add_dotProduct, smul_dotProduct, hRA' j hj, (ih1 j hj).2.2]; simp
            · subst hj
              by_cases h0 : α j = 0
              · rw [hαP j h0]; simp
              · have e : α j • (A *ᵥ P j) = R j - R (j+1) := by rw [hRs]; abel
                have h1 : α j * (R (j+1) ⬝ᵥ (A *ᵥ P j)) = - (R (j+1) ⬝ᵥ R (j+1)) := by
                  rw [← smul_eq_mul, ← dotProduct_smul, e, dotProduct_sub, hb j (by omega)]
                  simp
                have hp : P j ≠ 0 := by
                  intro hp; apply h0; rw [hα, hp]; simp
                have hpp := hpos _ hp
                have hrr : R j ⬝ᵥ R j ≠ 0 := by
                  intro hr; apply h0; rw [hα, hr]; simp
                rw [hPs, add_dotProduct, smul_dotProduct, hβ, smul_eq_mul]
                rw [hα] at h1
                field_simp at h1 ⊢
                linear_combination h1
          · rw [hPs, dotProduct_add, dotProduct_smul, hii]; simp
      have hRRpos : ∀ i < m, 0 < R i ⬝ᵥ R i := by
        intro i hi
        rcases (hself (R i)).lt_or_eq with h1 | h1
        · exact h1
        · exact absurd (hzero _ h1.symm) (hact i hi)
      have hPne : ∀ i < m, P i ≠ 0 := by
        intro i hi hp
        have hr := hRRpos i hi
        have := (hQ i).2
        rw [hp] at this; simp at this; linarith
      have hPPpos : ∀ i < m, 0 < P i ⬝ᵥ P i := by
        intro i hi
        rcases (hself (P i)).lt_or_eq with h1 | h1
        · exact h1
        · exact absurd (hzero _ h1.symm) (hPne i hi)
      have hRnext : ∀ i, R i = 0 → R (i+1) = 0 := by
        intro i hi
        rw [hRs, hRP0 i hi, hi]; simp
      -- P (i+1) ⬝ P (i+1) expansion
      have hpp : ∀ i, P (i + 1) ⬝ᵥ P (i + 1) = R (i + 1) ⬝ᵥ R (i + 1) + β i ^ 2 * (P i ⬝ᵥ P i) := by
        intro i
        have h0 : R (i+1) ⬝ᵥ P i = 0 := ((hQ (i+1)).1 i (by omega)).1
        rw [hPs, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, smul_dotProduct,
          dotProduct_smul, dotProduct_smul, h0, dotProduct_comm (P i) (R (i+1)), h0]
        simp only [smul_eq_mul]; ring
      -- conjugacy symmetric form
      have hconj : ∀ a b, a ≠ b → P a ⬝ᵥ (A *ᵥ P b) = 0 := by
        intro a b hab
        rcases lt_or_gt_of_ne hab with h | h
        · rw [hsym]; exact ((hQ b).1 a h).2.2
        · exact ((hQ a).1 b h).2.2
      -- R i ⬝ A P b = 0 for i < b
      have hRAP : ∀ i b, i < b → R i ⬝ᵥ (A *ᵥ P b) = 0 := by
        intro i b hib
        cases i with
        | zero => rw [← hP0]; exact hconj 0 b (by omega)
        | succ i =>
          have e : R (i+1) = P (i+1) - β i • P i := by rw [hPs]; abel
          rw [e, sub_dotProduct, smul_dotProduct, hconj _ _ (by omega), hconj _ _ (by omega)]
          simp
      have part1 : ∀ i j : ℕ, i ≤ j → P i ⬝ᵥ P j = (R j ⬝ᵥ R j) * (P i ⬝ᵥ P i) / (R i ⬝ᵥ R i) := by
        intro i j hij
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
        induction d with
        | zero =>
          simp only [add_zero]
          by_cases hr : R i ⬝ᵥ R i = 0
          · rw [hRP0 i (hzero _ hr)]; simp
          · field_simp
        | succ d ih =>
          have ih := ih (by omega)
          have h0 : P i ⬝ᵥ R (i + d + 1) = 0 := by
            rw [dotProduct_comm]; exact ((hQ (i+d+1)).1 i (by omega)).1
          rw [show i + (d+1) = (i + d) + 1 by ring, hPs, dotProduct_add, dotProduct_smul, h0, ih,
            hβ, smul_eq_mul]
          by_cases hr : R (i + d) ⬝ᵥ R (i + d) = 0
          · rw [hRnext _ (hzero _ hr)]; simp
          · rw [zero_add]; field_simp
      refine ⟨part1, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        refine ⟨hpp i, ?_⟩
        have hS : ∀ i, P i ⬝ᵥ P i = (R i ⬝ᵥ R i) ^ 2 * ∑ j ∈ Finset.range (i + 1), 1 / (R j ⬝ᵥ R j) := by
          intro i
          induction i with
          | zero =>
            simp [hP0]
            by_cases hr : R 0 ⬝ᵥ R 0 = 0
            · rw [hr]; simp
            · field_simp
          | succ i ih =>
            rw [hpp, ih, hβ, Finset.sum_range_succ _ (i + 1)]
            by_cases hr : R i ⬝ᵥ R i = 0
            · rw [hRnext _ (hzero _ hr)]; simp
            · by_cases hr' : R (i+1) ⬝ᵥ R (i+1) = 0
              · rw [hr']; simp
              · field_simp
                ring
        exact hS (i + 1)
      · intro i j hij
        have main : ∀ i j, i + 1 < j → R i ⬝ᵥ (A *ᵥ R j) = 0 := by
          intro i j hij
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          have e : R (j'+1) = P (j'+1) - β j' • P j' := by rw [hPs]; abel
          rw [e, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
            hRAP _ _ (by omega), hRAP _ _ (by omega)]
          simp
        rcases hij with h | h
        · exact main i j h
        · rw [hsym]; exact main j i h
      · intro i
        have e : R (i+1) = P (i+1) - β i • P i := by rw [hPs]; abel
        rw [e]
        simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
          dotProduct_smul, smul_dotProduct, smul_eq_mul]
        rw [hconj (i+1) i (by omega), hconj i (i+1) (by omega)]
        ring
      · intro i
        cases i with
        | zero => rw [hP0]
        | succ i =>
          rw [hpp]
          have := hself (P i)
          nlinarith [sq_nonneg (β i)]
      · intro i hi0 him
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [hpp]
        have hb : 0 < β i' := by
          rw [hβ]; exact div_pos (hRRpos _ him) (hRRpos _ (by omega))
        have := hPPpos i' (by omega)
        have : 0 < β i' ^ 2 * (P i' ⬝ᵥ P i') := by positivity
        linarith
      · intro i j hi hj
        have p1 : ∀ i j : ℕ, i ≤ j → j < m → 0 < P i ⬝ᵥ P j := by
          intro i j hij hj
          rw [part1 i j hij]
          have := hRRpos j hj
          have := hRRpos i (by omega)
          have := hPPpos i (by omega)
          positivity
        rcases le_total i j with h | h
        · exact p1 i j h hj
        · rw [dotProduct_comm]; exact p1 j i h hi
