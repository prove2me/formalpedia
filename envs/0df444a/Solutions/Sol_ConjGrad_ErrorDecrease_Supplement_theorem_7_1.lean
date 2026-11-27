-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_7_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:55.469537+00:00
-- url     : https://prove2.me/submissions/ce45e187-2ad9-4bef-8fe0-77a4a13477de

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 7:1 (Hestenes–Stiefel 1952, p. 418): `pᵢ = cᵢ(k − Ax̄ᵢ)` (7:1) for `cᵢ`, `x̄ᵢ` given by
(7:2), and the closed forms (7:3a)–(7:3c) with coefficients summing to one before termination;
`m` is the step at which the cg-method terminates. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ, (cgIter A k x₀ i).p = smoothC A k x₀ i • (k - A *ᵥ smoothX A k x₀ i)) ∧
    (smoothC A k x₀ 0 = 1 ∧ smoothX A k x₀ 0 = x₀ ∧
      ∀ i : ℕ, smoothC A k x₀ (i + 1) = 1 + cgBeta A k x₀ i * smoothC A k x₀ i ∧
        smoothX A k x₀ (i + 1) = (1 / smoothC A k x₀ (i + 1)) •
          ((cgIter A k x₀ (i + 1)).x + (cgBeta A k x₀ i * smoothC A k x₀ i) • smoothX A k x₀ i)) ∧
    (∀ i : ℕ, i < m →
      smoothC A k x₀ i = ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) *
          ∑ j ∈ Finset.range (i + 1), 1 / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r) ∧
        smoothC A k x₀ i = ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) /
          ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r)) ∧
    (∀ i : ℕ, i < m →
      smoothX A k x₀ i = (((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) / smoothC A k x₀ i) •
        ∑ j ∈ Finset.range (i + 1),
          (1 / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).x) ∧
    (∀ i : ℕ, k - A *ᵥ smoothX A k x₀ i = (1 / smoothC A k x₀ i) • (cgIter A k x₀ i).p) ∧
    (∀ i : ℕ, i < m →
      k - A *ᵥ smoothX A k x₀ i =
        (((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) / smoothC A k x₀ i) •
          ∑ j ∈ Finset.range (i + 1),
            (1 / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).r) ∧
    (∀ i : ℕ, i < m →
      ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) / smoothC A k x₀ i *
        ∑ j ∈ Finset.range (i + 1), 1 / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r) = 1) := by
          have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
            intro u v
            have hT : Aᵀ = A := by
              have := hA.1
              rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
            rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
          have hpos : ∀ w : Fin n → ℝ, w ≠ 0 → 0 < w ⬝ᵥ (A *ᵥ w) := by
            intro w hw
            simpa using hA.dotProduct_mulVec_pos hw
          have hnn : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ (A *ᵥ w) := by
            intro w
            by_cases hw : w = 0
            · simp [hw]
            · exact (hpos w hw).le
          have hzero : ∀ w : Fin n → ℝ, w ⬝ᵥ w = 0 → w = 0 := fun w hw => dotProduct_self_eq_zero.mp hw
          have hself : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ w := fun w =>
            Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
          suffices key : ∀ (X R P : ℕ → (Fin n → ℝ)) (α β C : ℕ → ℝ) (Xb : ℕ → (Fin n → ℝ)),
              X 0 = x₀ → R 0 = k - A *ᵥ X 0 → P 0 = R 0 →
              (∀ i, α i = R i ⬝ᵥ R i / (P i ⬝ᵥ (A *ᵥ P i))) →
              (∀ i, β i = R (i+1) ⬝ᵥ R (i+1) / (R i ⬝ᵥ R i)) →
              (∀ i, X (i+1) = X i + α i • P i) →
              (∀ i, R (i+1) = R i - α i • (A *ᵥ P i)) →
              (∀ i, P (i+1) = R (i+1) + β i • P i) →
              C 0 = 1 → Xb 0 = x₀ →
              (∀ i, C (i+1) = 1 + β i * C i) →
              (∀ i, Xb (i+1) = (1 + β i * C i)⁻¹ • (X (i+1) + (β i * C i) • Xb i)) →
              R m = 0 → (∀ j < m, R j ≠ 0) →
            (∀ i : ℕ, P i = C i • (k - A *ᵥ Xb i)) ∧
            (C 0 = 1 ∧ Xb 0 = x₀ ∧
              ∀ i : ℕ, C (i + 1) = 1 + β i * C i ∧
                Xb (i + 1) = (1 / C (i + 1)) • (X (i + 1) + (β i * C i) • Xb i)) ∧
            (∀ i : ℕ, i < m →
              C i = (R i ⬝ᵥ R i) * ∑ j ∈ Finset.range (i + 1), 1 / (R j ⬝ᵥ R j) ∧
                C i = (P i ⬝ᵥ P i) / (R i ⬝ᵥ R i)) ∧
            (∀ i : ℕ, i < m →
              Xb i = ((R i ⬝ᵥ R i) / C i) • ∑ j ∈ Finset.range (i + 1), (1 / (R j ⬝ᵥ R j)) • X j) ∧
            (∀ i : ℕ, k - A *ᵥ Xb i = (1 / C i) • P i) ∧
            (∀ i : ℕ, i < m →
              k - A *ᵥ Xb i = ((R i ⬝ᵥ R i) / C i) • ∑ j ∈ Finset.range (i + 1), (1 / (R j ⬝ᵥ R j)) • R j) ∧
            (∀ i : ℕ, i < m →
              (R i ⬝ᵥ R i) / C i * ∑ j ∈ Finset.range (i + 1), 1 / (R j ⬝ᵥ R j) = 1) by
            exact key (fun i => (cgIter A k x₀ i).x) (fun i => (cgIter A k x₀ i).r)
              (fun i => (cgIter A k x₀ i).p) (fun i => cgAlpha A (cgIter A k x₀ i))
              (fun i => cgBeta A k x₀ i) (fun i => smoothC A k x₀ i) (fun i => smoothX A k x₀ i)
              rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
              rfl rfl (fun _ => rfl) (fun _ => rfl)
              hm hact
          intro X R P α β C Xb hX0 hR0 hP0 hα hβ hX hRs hPs hC0 hXb0 hCs hXbs hm hact
          have hRX : ∀ i, R i = k - A *ᵥ X i := by
            intro i
            induction i with
            | zero => exact hR0
            | succ i ih =>
              rw [hRs, hX, ih, Matrix.mulVec_add, Matrix.mulVec_smul]; abel
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
          have hN : ∀ i < m, 0 < R i ⬝ᵥ R i := by
            intro i hi
            rcases (hself (R i)).lt_or_eq with h1 | h1
            · exact h1
            · exact absurd (hzero _ h1.symm) (hact i hi)
          have hβnn : ∀ i, 0 ≤ β i := fun i => by rw [hβ]; exact div_nonneg (hself _) (hself _)
          have hC1 : ∀ i, 1 ≤ C i := by
            intro i
            induction i with
            | zero => rw [hC0]
            | succ i ih => rw [hCs]; nlinarith [hβnn i]
          have hCne : ∀ i, C i ≠ 0 := fun i => by linarith [hC1 i]
          have hXb' : ∀ i, Xb (i+1) = (C (i+1))⁻¹ • (X (i+1) + (β i * C i) • Xb i) := by
            intro i; rw [hXbs, hCs]
          have hRX' := hRX
          have part1 : ∀ i : ℕ, P i = C i • (k - A *ᵥ Xb i) := by
            intro i
            induction i with
            | zero => rw [hP0, hR0, hC0, hXb0, hX0, one_smul]
            | succ i ih =>
              rw [hXb' i, Matrix.mulVec_smul, smul_sub, smul_smul, mul_inv_cancel₀ (hCne _), one_smul,
                Matrix.mulVec_add, Matrix.mulVec_smul, hPs, ih, hRX (i+1), hCs]
              module
          have part5 : ∀ i : ℕ, k - A *ᵥ Xb i = (1 / C i) • P i := by
            intro i
            rw [part1 i, smul_smul, one_div, inv_mul_cancel₀ (hCne _), one_smul]
          have hRP : ∀ i, R (i+1) ⬝ᵥ P i = 0 := fun i => ((hQ (i+1)).1 i (Nat.lt_succ_self i)).1
          have part3a : ∀ i : ℕ, i < m →
              C i = (R i ⬝ᵥ R i) * ∑ j ∈ Finset.range (i + 1), 1 / (R j ⬝ᵥ R j) := by
            intro i
            induction i with
            | zero => intro _; rw [hC0, Finset.sum_range_one]; have := hN 0 (by omega); field_simp
            | succ i ih =>
              intro hi
              have h0 := hN i (by omega)
              have h1 := hN (i+1) hi
              rw [hCs, hβ, ih (by omega), Finset.sum_range_succ _ (i+1)]
              field_simp
              ring
          have part3b : ∀ i : ℕ, i < m → C i * (R i ⬝ᵥ R i) = P i ⬝ᵥ P i := by
            intro i
            induction i with
            | zero => intro _; rw [hC0, hP0, one_mul]
            | succ i ih =>
              intro hi
              have h0 := hN i (by omega)
              have h1 := hN (i+1) hi
              have e := ih (by omega)
              have hrp := hRP i
              have hpr : P i ⬝ᵥ R (i+1) = 0 := by rw [dotProduct_comm]; exact hrp
              rw [hPs (i), dotProduct_add, add_dotProduct, add_dotProduct, dotProduct_smul,
                dotProduct_smul, smul_dotProduct, smul_dotProduct, hrp, hpr, ← e, hCs, hβ]
              simp only [smul_eq_mul]
              field_simp
              ring
          have part4' : ∀ i : ℕ, i < m →
              C i • Xb i = (R i ⬝ᵥ R i) • ∑ j ∈ Finset.range (i + 1), (1 / (R j ⬝ᵥ R j)) • X j := by
            intro i
            induction i with
            | zero => intro _; rw [hC0, hXb0, Finset.sum_range_one, smul_smul, hX0, one_smul]; have := hN 0 (by omega); field_simp; simp
            | succ i ih =>
              intro hi
              have h0 := hN i (by omega)
              have h1 := hN (i+1) hi
              rw [hXb' i, smul_smul, mul_inv_cancel₀ (hCne _), one_smul, mul_smul,
                ih (by omega), Finset.sum_range_succ _ (i+1), smul_add]
              simp only [smul_smul]
              rw [hβ]
              have e1 : R (i+1) ⬝ᵥ R (i+1) / (R i ⬝ᵥ R i) * (R i ⬝ᵥ R i) = R (i+1) ⬝ᵥ R (i+1) := by
                field_simp
              have e2 : R (i+1) ⬝ᵥ R (i+1) * (1 / (R (i+1) ⬝ᵥ R (i+1))) = 1 := by
                field_simp
              rw [e1, e2, one_smul, add_comm]
          have part4 : ∀ i : ℕ, i < m →
              Xb i = ((R i ⬝ᵥ R i) / C i) • ∑ j ∈ Finset.range (i + 1), (1 / (R j ⬝ᵥ R j)) • X j := by
            intro i hi
            rw [div_eq_inv_mul, ← smul_smul, ← part4' i hi, smul_smul, inv_mul_cancel₀ (hCne _), one_smul]
          have part7 : ∀ i : ℕ, i < m →
              (R i ⬝ᵥ R i) / C i * ∑ j ∈ Finset.range (i + 1), 1 / (R j ⬝ᵥ R j) = 1 := by
            intro i hi
            have := hCne i
            rw [part3a i hi] at this ⊢
            have h0 := hN i hi
            have hS := right_ne_zero_of_mul this
            field_simp
          have hR' : ∀ j, (1 / (R j ⬝ᵥ R j)) • R j =
              (1 / (R j ⬝ᵥ R j)) • k - A *ᵥ ((1 / (R j ⬝ᵥ R j)) • X j) := by
            intro j
            generalize 1 / (R j ⬝ᵥ R j) = c
            rw [hRX j, Matrix.mulVec_smul, smul_sub]
          have hsumR : ∀ i : ℕ, ∑ j ∈ Finset.range (i + 1), (1 / (R j ⬝ᵥ R j)) • R j =
              (∑ j ∈ Finset.range (i + 1), 1 / (R j ⬝ᵥ R j)) • k -
                A *ᵥ ∑ j ∈ Finset.range (i + 1), (1 / (R j ⬝ᵥ R j)) • X j := by
            intro i
            induction i with
            | zero => simp only [zero_add, Finset.sum_range_one]; exact hR' 0
            | succ i ih =>
              rw [Finset.sum_range_succ _ (i+1), Finset.sum_range_succ _ (i+1),
                Finset.sum_range_succ _ (i+1), ih, hR' (i+1), Matrix.mulVec_add, add_smul]
              module
          have part6 : ∀ i : ℕ, i < m →
              k - A *ᵥ Xb i = ((R i ⬝ᵥ R i) / C i) •
                ∑ j ∈ Finset.range (i + 1), (1 / (R j ⬝ᵥ R j)) • R j := by
            intro i hi
            rw [hsumR, smul_sub, smul_smul, part7 i hi, one_smul, ← Matrix.mulVec_smul, ← part4 i hi]
          refine ⟨part1, ⟨hC0, hXb0, fun i => ⟨hCs i, by rw [hXbs, ← hCs, one_div]⟩⟩,
            fun i hi => ⟨part3a i hi, ?_⟩, part4, part5, part6, part7⟩
          have := part3b i hi
          have h0 := hN i hi
          rw [← this]; field_simp
