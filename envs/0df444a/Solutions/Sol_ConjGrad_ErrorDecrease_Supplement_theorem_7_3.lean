-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_7_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:17.424942+00:00
-- url     : https://prove2.me/submissions/2d8e2c5c-10f2-4121-bb37-142c226da347

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 7:3 (Hestenes–Stiefel 1952, p. 419): (7:6a) at the paper's index `i + 1` with
`0 < i + 1 < m`, (7:6b) for `i < m`, and `μ(r̄ᵢ) < μ(rᵢ)` for `0 < i < m`, where
`r̄ᵢ = k − Ax̄ᵢ` and `m` is the step at which the cg-method terminates. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ, i + 1 < m →
      rayleigh A (cgIter A k x₀ (i + 1)).r /
          ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) =
        rayleigh A (k - A *ᵥ smoothX A k x₀ (i + 1)) /
            ((k - A *ᵥ smoothX A k x₀ (i + 1)) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ (i + 1))) +
          rayleigh A (k - A *ᵥ smoothX A k x₀ i) /
            ((k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i))) ∧
    (∀ i : ℕ, i < m →
      rayleigh A (k - A *ᵥ smoothX A k x₀ i) /
          ((k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i)) =
        ∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ (i + j) *
          (rayleigh A (cgIter A k x₀ j).r / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r))) ∧
    (∀ i : ℕ, 0 < i → i < m →
      rayleigh A (k - A *ᵥ smoothX A k x₀ i) < rayleigh A (cgIter A k x₀ i).r) := by
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
          (∀ i : ℕ, i + 1 < m →
            rayleigh A (R (i + 1)) / (R (i + 1) ⬝ᵥ R (i + 1)) =
              rayleigh A (k - A *ᵥ Xb (i + 1)) / ((k - A *ᵥ Xb (i + 1)) ⬝ᵥ (k - A *ᵥ Xb (i + 1))) +
                rayleigh A (k - A *ᵥ Xb i) / ((k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i))) ∧
          (∀ i : ℕ, i < m →
            rayleigh A (k - A *ᵥ Xb i) / ((k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i)) =
              ∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ (i + j) * (rayleigh A (R j) / (R j ⬝ᵥ R j))) ∧
          (∀ i : ℕ, 0 < i → i < m → rayleigh A (k - A *ᵥ Xb i) < rayleigh A (R i)) by
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
        have hdpos : ∀ i < m, 0 < P i ⬝ᵥ (A *ᵥ P i) := by
          intro i hi
          apply hpos
          intro hp
          have h1 := (hQ i).2
          rw [hp, dotProduct_zero] at h1
          exact (hN i hi).ne h1
        have hrayP : ∀ i < m, rayleigh A (k - A *ᵥ Xb i) = P i ⬝ᵥ (A *ᵥ P i) / (C i * (R i ⬝ᵥ R i)) := by
          intro i hi
          have hc := hCne i
          have hs := (hN i hi).ne'
          rw [part5 i]
          unfold rayleigh
          simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
          rw [← part3b i hi]
          field_simp
        have hq : ∀ i < m, rayleigh A (k - A *ᵥ Xb i) / ((k - A *ᵥ Xb i) ⬝ᵥ (k - A *ᵥ Xb i)) =
            P i ⬝ᵥ (A *ᵥ P i) / (R i ⬝ᵥ R i) / (R i ⬝ᵥ R i) := by
          intro i hi
          have hc := hCne i
          have hs := (hN i hi).ne'
          rw [hrayP i hi, part5 i]
          simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
          rw [← part3b i hi]
          field_simp
        have hRR : ∀ i, R (i+1) ⬝ᵥ (A *ᵥ R (i+1)) =
            P (i+1) ⬝ᵥ (A *ᵥ P (i+1)) + β i ^ 2 * (P i ⬝ᵥ (A *ᵥ P i)) := by
          intro i
          have e : R (i+1) = P (i+1) - β i • P i := by rw [hPs]; abel
          have h1 : P (i+1) ⬝ᵥ (A *ᵥ P i) = 0 := ((hQ (i+1)).1 i (Nat.lt_succ_self i)).2.2
          have h2 : P i ⬝ᵥ (A *ᵥ P (i+1)) = 0 := by rw [hsym]; exact h1
          rw [e, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct, sub_dotProduct,
            dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_dotProduct, h1, h2]
          simp only [smul_eq_mul]
          ring
        have hν : ∀ i, i + 1 < m → rayleigh A (R (i+1)) / (R (i+1) ⬝ᵥ R (i+1)) =
            P (i+1) ⬝ᵥ (A *ᵥ P (i+1)) / (R (i+1) ⬝ᵥ R (i+1)) / (R (i+1) ⬝ᵥ R (i+1)) +
              P i ⬝ᵥ (A *ᵥ P i) / (R i ⬝ᵥ R i) / (R i ⬝ᵥ R i) := by
          intro i hi
          have h0 := (hN i (by omega)).ne'
          have h1 := (hN (i+1) hi).ne'
          unfold rayleigh
          rw [hRR, hβ]
          field_simp
        refine ⟨?_, ?_, ?_⟩
        · intro i hi
          rw [hν i hi, hq (i+1) hi, hq i (by omega)]
        · intro i
          induction i with
          | zero =>
            intro h
            rw [hq 0 h, Finset.sum_range_one]
            unfold rayleigh
            rw [hP0]
            simp
          | succ i ih =>
            intro hi
            have ih' := ih (by omega)
            rw [hq i (by omega)] at ih'
            have hneg : ∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ (i + 1 + j) *
                (rayleigh A (R j) / (R j ⬝ᵥ R j)) =
                -∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ (i + j) * (rayleigh A (R j) / (R j ⬝ᵥ R j)) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro j _
              rw [show i + 1 + j = (i + j) + 1 by ring, pow_succ]
              ring
            have hone : (-1 : ℝ) ^ (i + 1 + (i + 1)) = 1 := by
              rw [show i + 1 + (i + 1) = 2 * (i + 1) by ring, pow_mul]
              norm_num
            rw [Finset.sum_range_succ, hneg, ← ih', hone, one_mul, hq (i+1) hi, hν i hi]
            ring
        · intro i h0 hi
          obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          rw [hrayP (j+1) hi]
          unfold rayleigh
          rw [hRR j]
          have hs0 := hN j (by omega)
          have hs1 := hN (j+1) hi
          have hd0 := hdpos j (by omega)
          have hd1 := hdpos (j+1) hi
          have hC := hC1 (j+1)
          have hb : 0 < β j := by rw [hβ]; exact div_pos hs1 hs0
          have hCs' : 0 < C (j+1) * (R (j+1) ⬝ᵥ R (j+1)) := by positivity
          rw [div_lt_div_iff₀ hCs' hs1]
          have e1 : 0 < β j ^ 2 * (P j ⬝ᵥ (A *ᵥ P j)) * (C (j+1) * (R (j+1) ⬝ᵥ R (j+1))) := by positivity
          have e2 := mul_nonneg (mul_nonneg hd1.le hs1.le) (sub_nonneg.mpr hC)
          nlinarith [e1, e2]
