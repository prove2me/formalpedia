-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:22.022242+00:00
-- url     : https://prove2.me/submissions/c8972a85-0c9e-4bb5-b17f-2844f8bc5b72

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 6:1 (Hestenes–Stiefel 1952, p. 416): distinct estimates up to termination, minimization
of `f` on the plane `Pᵢ`, (6:1), (6:2) and both expansions (6:3); `m` is the step at which the
cg-method terminates. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i j : ℕ, i ≤ m → j ≤ m → i ≠ j → (cgIter A k x₀ i).x ≠ (cgIter A k x₀ j).x) ∧
    (∀ i : ℕ, (cgIter A k x₀ i).x ∈ cdPlane x₀ (fun j => (cgIter A k x₀ j).p) i ∧
      ∀ y ∈ cdPlane x₀ (fun j => (cgIter A k x₀ j).p) i,
        errorFun A h (cgIter A k x₀ i).x ≤ errorFun A h y) ∧
    (∀ i : ℕ, ∀ j ≤ i, (cgIter A k x₀ j).x ∈ cdPlane x₀ (fun j => (cgIter A k x₀ j).p) i) ∧
    (∀ i ≤ m, LinearIndependent ℝ (fun j : Fin i => (cgIter A k x₀ j).p)) ∧
    (∀ i : ℕ,
      errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ (i + 1)).x =
        cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) ∧
      cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) =
        rayleigh A (cgIter A k x₀ i).p *
          (((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x) ⬝ᵥ
            ((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x))) ∧
    (∀ i j : ℕ, i < j →
      errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ j).x =
        ∑ l ∈ Finset.Ico i j,
          cgAlpha A (cgIter A k x₀ l) * ((cgIter A k x₀ l).r ⬝ᵥ (cgIter A k x₀ l).r)) ∧
    (∀ i : ℕ,
      (cgIter A k x₀ i).x = x₀ + ∑ j ∈ Finset.range i,
        cgAlpha A (cgIter A k x₀ j) • (cgIter A k x₀ j).p ∧
      (cgIter A k x₀ i).x = x₀ + ∑ j ∈ Finset.range i,
        ((errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ i).x) /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).r) := by
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
            have hself : ∀ w : Fin n → ℝ, 0 ≤ w ⬝ᵥ w := fun w =>
              Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
            have hzero : ∀ w : Fin n → ℝ, w ⬝ᵥ w = 0 → w = 0 := fun w hw => dotProduct_self_eq_zero.mp hw
            suffices key : ∀ (X R P : ℕ → (Fin n → ℝ)) (α β : ℕ → ℝ),
                X 0 = x₀ → R 0 = k - A *ᵥ X 0 → P 0 = R 0 →
                (∀ i, α i = R i ⬝ᵥ R i / (P i ⬝ᵥ (A *ᵥ P i))) →
                (∀ i, β i = R (i+1) ⬝ᵥ R (i+1) / (R i ⬝ᵥ R i)) →
                (∀ i, X (i+1) = X i + α i • P i) →
                (∀ i, R (i+1) = R i - α i • (A *ᵥ P i)) →
                (∀ i, P (i+1) = R (i+1) + β i • P i) →
                R m = 0 → (∀ j < m, R j ≠ 0) →
              (∀ i j : ℕ, i ≤ m → j ≤ m → i ≠ j → X i ≠ X j) ∧
              (∀ i : ℕ, X i ∈ cdPlane x₀ P i ∧ ∀ y ∈ cdPlane x₀ P i, errorFun A h (X i) ≤ errorFun A h y) ∧
              (∀ i : ℕ, ∀ j ≤ i, X j ∈ cdPlane x₀ P i) ∧
              (∀ i ≤ m, LinearIndependent ℝ (fun j : Fin i => P j)) ∧
              (∀ i : ℕ, errorFun A h (X i) - errorFun A h (X (i + 1)) = α i * (R i ⬝ᵥ R i) ∧
                α i * (R i ⬝ᵥ R i) = rayleigh A (P i) * ((X i - X (i + 1)) ⬝ᵥ (X i - X (i + 1)))) ∧
              (∀ i j : ℕ, i < j → errorFun A h (X i) - errorFun A h (X j) =
                  ∑ l ∈ Finset.Ico i j, α l * (R l ⬝ᵥ R l)) ∧
              (∀ i : ℕ, X i = x₀ + ∑ j ∈ Finset.range i, α j • P j ∧
                X i = x₀ + ∑ j ∈ Finset.range i,
                  ((errorFun A h (X j) - errorFun A h (X i)) / (R j ⬝ᵥ R j)) • R j) by
              exact key (fun i => (cgIter A k x₀ i).x) (fun i => (cgIter A k x₀ i).r)
                (fun i => (cgIter A k x₀ i).p) (fun i => cgAlpha A (cgIter A k x₀ i))
                (fun i => (cgIter A k x₀ (i+1)).r ⬝ᵥ (cgIter A k x₀ (i+1)).r /
                  ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r))
                rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
                hm hact
            intro X R P α β hX0 hR0 hP0 hα hβ hX hRs hPs hm hact
            have hRX : ∀ i, R i = k - A *ᵥ X i := by
              intro i
              induction i with
              | zero => exact hR0
              | succ i ih =>
                rw [hRs, hX, ih, Matrix.mulVec_add, Matrix.mulVec_smul]; abel
            have hAE : ∀ i, A *ᵥ (h - X i) = R i := by
              intro i; rw [Matrix.mulVec_sub, hh, hRX]
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
            -- decrease of the error function
            have hdec : ∀ i, errorFun A h (X i) - errorFun A h (X (i+1)) = α i * (R i ⬝ᵥ R i) := by
              intro i
              have hαe : α i * (α i * (P i ⬝ᵥ (A *ᵥ P i))) = α i * (R i ⬝ᵥ R i) := by
                by_cases hz : P i ⬝ᵥ (A *ᵥ P i) = 0
                · simp [hα i, hz]
                · rw [hα i]; field_simp
              have hz1 : P i ⬝ᵥ R (i+1) = 0 := by
                rw [dotProduct_comm]; exact ((hQ (i+1)).1 i (by omega)).1
              have hz2 : (h - X (i+1)) ⬝ᵥ (A *ᵥ P i) = 0 := by
                rw [hsym, hAE]; exact hz1
              have e : h - X i = (h - X (i+1)) + α i • P i := by rw [hX]; abel
              unfold errorFun
              rw [e]
              simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
                smul_dotProduct, dotProduct_smul, smul_eq_mul, hAE, hz1, hz2]
              linear_combination hαe
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
            have hαpos : ∀ i < m, 0 < α i := by
              intro i hi
              rw [hα]; exact div_pos (hRRpos i hi) (hpos _ (hPne i hi))
            have hcpos : ∀ i < m, 0 < α i * (R i ⬝ᵥ R i) := fun i hi => mul_pos (hαpos i hi) (hRRpos i hi)
            have hXs : ∀ a d, X (a+d) = X a + ∑ l ∈ Finset.range d, α (a+l) • P (a+l) := by
              intro a d
              induction d with
              | zero => simp
              | succ d ih =>
                rw [Finset.sum_range_succ, ← add_assoc, hX, ih, add_assoc]
            have hX0s : ∀ i, X i = x₀ + ∑ j ∈ Finset.range i, α j • P j := by
              intro i; have := hXs 0 i; simpa [hX0] using this
            have hRstay : ∀ i, R i = 0 → R (i+1) = 0 := by
              intro i hi; rw [hRs, hi, hRP0 i hi]; simp
            have hRbig : ∀ d, R (m + d) = 0 := by
              intro d
              induction d with
              | zero => simpa using hm
              | succ d ih => rw [← add_assoc]; exact hRstay _ ih
            have hsumg : ∀ a d, errorFun A h (X a) - errorFun A h (X (a+d)) =
                ∑ l ∈ Finset.range d, α (a+l) * (R (a+l) ⬝ᵥ R (a+l)) := by
              intro a d
              induction d with
              | zero => simp
              | succ d ih =>
                rw [Finset.sum_range_succ, ← ih, ← hdec (a+d), ← add_assoc]
                ring
            have hIco : ∀ i j : ℕ, i < j → errorFun A h (X i) - errorFun A h (X j) =
                ∑ l ∈ Finset.Ico i j, α l * (R l ⬝ᵥ R l) := by
              intro i j hij
              obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
              rw [hsumg i d, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
            have hmono : ∀ i j, i < j → j ≤ m → errorFun A h (X j) < errorFun A h (X i) := by
              intro i j hij hj
              have := hIco i j hij
              have hp : 0 < ∑ l ∈ Finset.Ico i j, α l * (R l ⬝ᵥ R l) := by
                apply Finset.sum_pos
                · intro l hl
                  rw [Finset.mem_Ico] at hl
                  exact hcpos _ (by omega)
                · exact ⟨i, by rw [Finset.mem_Ico]; omega⟩
              linarith
            -- conjugacy, symmetric form
            have hconj : ∀ i j, i ≠ j → P i ⬝ᵥ (A *ᵥ P j) = 0 := by
              intro i j hij
              rcases lt_or_gt_of_ne hij with hl | hl
              · rw [hsym]; exact ((hQ j).1 i hl).2.2
              · exact ((hQ i).1 j hl).2.2
            -- expansion of P in residuals
            have hPexp : ∀ i < m, P i = (R i ⬝ᵥ R i) • ∑ j ∈ Finset.range (i+1), (1 / (R j ⬝ᵥ R j)) • R j := by
              intro i
              induction i with
              | zero =>
                intro hi
                have := hRRpos 0 hi
                rw [Finset.sum_range_one, smul_smul, mul_one_div_cancel this.ne', one_smul, hP0]
              | succ i ih =>
                intro hi
                have h1 := hRRpos i (by omega)
                have h2 := hRRpos (i+1) hi
                rw [hPs, ih (by omega), hβ, Finset.sum_range_succ _ (i+1), smul_smul, smul_add, smul_smul,
                  div_mul_cancel₀ _ h1.ne', mul_one_div_cancel h2.ne', one_smul, add_comm]
            have haP : ∀ i, α i • P i =
                (α i * (R i ⬝ᵥ R i)) • ∑ j ∈ Finset.range (i+1), (1 / (R j ⬝ᵥ R j)) • R j := by
              intro i
              by_cases hi : i < m
              · rw [hPexp i hi, smul_smul]
              · obtain ⟨d, rfl⟩ : ∃ d, i = m + d := ⟨i - m, by omega⟩
                rw [hRbig d, hRP0 _ (hRbig d)]
                simp
            have hexp2 : ∀ i, ∑ j ∈ Finset.range i, α j • P j = ∑ j ∈ Finset.range i,
                  ((errorFun A h (X j) - errorFun A h (X i)) / (R j ⬝ᵥ R j)) • R j := by
              intro i
              induction i with
              | zero => simp
              | succ i ih =>
                have e1 : ∑ j ∈ Finset.range (i+1),
                    ((errorFun A h (X j) - errorFun A h (X (i+1))) / (R j ⬝ᵥ R j)) • R j =
                    ∑ j ∈ Finset.range (i+1),
                      ((errorFun A h (X j) - errorFun A h (X i)) / (R j ⬝ᵥ R j)) • R j +
                    (errorFun A h (X i) - errorFun A h (X (i+1))) •
                      ∑ j ∈ Finset.range (i+1), (1 / (R j ⬝ᵥ R j)) • R j := by
                  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro j _
                  rw [smul_smul, ← add_smul]
                  congr 1
                  ring
                rw [e1, hdec, ← haP, Finset.sum_range_succ (fun j =>
                    ((errorFun A h (X j) - errorFun A h (X i)) / (R j ⬝ᵥ R j)) • R j),
                  sub_self, zero_div, zero_smul, add_zero, ← ih, Finset.sum_range_succ]
            refine ⟨?_, ?_, ?_, ?_, ?_, hIco, ?_⟩
            · -- distinct
              intro i j hi hj hij he
              rcases lt_or_gt_of_ne hij with hl | hl
              · have := hmono i j hl hj; rw [he] at this; exact lt_irrefl _ this
              · have := hmono j i hl hi; rw [he] at this; exact lt_irrefl _ this
            · intro i
              refine ⟨⟨α, hX0s i⟩, ?_⟩
              rintro y ⟨γ, rfl⟩
              set d : Fin n → ℝ := ∑ j ∈ Finset.range i, (γ j - α j) • P j with hd
              have hy : x₀ + ∑ j ∈ Finset.range i, γ j • P j = X i + d := by
                rw [hX0s i, hd, add_assoc, ← Finset.sum_add_distrib]
                congr 1
                apply Finset.sum_congr rfl
                intro j _
                rw [← add_smul]; congr 1; ring
              have hdR : d ⬝ᵥ R i = 0 := by
                rw [hd, sum_dotProduct]
                apply Finset.sum_eq_zero
                intro j hj
                rw [Finset.mem_range] at hj
                rw [smul_dotProduct, dotProduct_comm, ((hQ i).1 j hj).1, smul_zero]
              have e : h - (X i + d) = (h - X i) - d := by abel
              have h3 : (h - X i) ⬝ᵥ (A *ᵥ d) = d ⬝ᵥ R i := by rw [hsym, hAE]
              rw [hy]
              unfold errorFun
              rw [e, Matrix.mulVec_sub A (h - X i) d, hAE, sub_dotProduct (h - X i) d (R i - A *ᵥ d),
                dotProduct_sub (h - X i) (R i) (A *ᵥ d), dotProduct_sub d (R i) (A *ᵥ d), h3, hdR]
              have := hnn d
              linarith
            · intro i j hj
              refine ⟨fun l => if l < j then α l else 0, ?_⟩
              rw [hX0s j]
              congr 1
              rw [← Finset.sum_subset (Finset.range_mono hj)]
              · apply Finset.sum_congr rfl
                intro l hl
                rw [Finset.mem_range] at hl
                simp [hl]
              · intro l _ hl
                rw [Finset.mem_range] at hl
                simp [hl]
            · intro i hi
              rw [linearIndependent_iff']
              intro s g hs l hl
              have hdot : (∑ j ∈ s, g j • P (j : ℕ)) ⬝ᵥ (A *ᵥ P (l : ℕ)) = 0 := by rw [hs]; simp
              rw [sum_dotProduct, Finset.sum_eq_single l] at hdot
              · rw [smul_dotProduct, smul_eq_mul] at hdot
                have hp := hpos _ (hPne l (by omega))
                rcases mul_eq_zero.mp hdot with h1 | h1
                · exact h1
                · linarith
              · intro b _ hb
                rw [smul_dotProduct, hconj _ _ (fun e => hb (Fin.ext e)), smul_zero]
              · intro hl'; exact absurd hl hl'
            · intro i
              refine ⟨hdec i, ?_⟩
              have e : X i - X (i+1) = (-α i) • P i := by rw [hX]; simp [neg_smul]
              rw [e, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
              unfold rayleigh
              by_cases hp : P i = 0
              · rw [hα i, hp]; simp
              · have h1 := hpos _ hp
                have h2 : 0 < P i ⬝ᵥ P i := by
                  rcases (hself (P i)).lt_or_eq with h | h
                  · exact h
                  · exact absurd (hzero _ h.symm) hp
                rw [hα i]
                field_simp
            · intro i
              exact ⟨hX0s i, (hX0s i).trans (by rw [hexp2 i])⟩
