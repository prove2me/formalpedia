-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_6_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:01.200826+00:00
-- url     : https://prove2.me/submissions/11977452-86ea-47f1-8ef7-47a96d9f2551

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 6:5 (Hestenes–Stiefel 1952, p. 417), at the paper's index `i = j + 1` with
`1 ≤ i < m`: the point `xₘ⁽ⁱ⁾ = xᵢ + (f(xᵢ)/|r_{i−1}|²) p_{i−1}` (6:8) is the unique nearest
point of `Pᵢ` to `h`, lies on the line `x_{i−1}xᵢ` beyond `xᵢ`, and satisfies (6:9), (6:10). -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) (j : ℕ) (hj : j + 1 < m) :
    (cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
        ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p ∈
      cdPlane x₀ (fun l => (cgIter A k x₀ l).p) (j + 1) ∧
    (∀ z ∈ cdPlane x₀ (fun l => (cgIter A k x₀ l).p) (j + 1),
      z ≠ (cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
        ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p →
      (h - ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p)) ⬝ᵥ
        (h - ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p)) <
      (h - z) ⬝ᵥ (h - z)) ∧
    (∃ t : ℝ, 1 < t ∧
      (cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p =
        (cgIter A k x₀ j).x + t • ((cgIter A k x₀ (j + 1)).x - (cgIter A k x₀ j).x)) ∧
    1 / errorFun A h ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
        ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p) =
      1 / errorFun A h (cgIter A k x₀ (j + 1)).x - 1 / errorFun A h (cgIter A k x₀ j).x ∧
    (h - (cgIter A k x₀ (j + 1)).x) ⬝ᵥ (h - (cgIter A k x₀ (j + 1)).x) =
      (h - ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p)) ⬝ᵥ
        (h - ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p)) +
      (errorFun A h ((cgIter A k x₀ (j + 1)).x + (errorFun A h (cgIter A k x₀ (j + 1)).x /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).p) -
        errorFun A h (cgIter A k x₀ (j + 1)).x) / rayleigh A (cgIter A k x₀ j).p := by
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
              (∀ j < m, R j ≠ 0) → R m = 0 →
            let y := X (j+1) + (errorFun A h (X (j+1)) / (R j ⬝ᵥ R j)) • P j
            y ∈ cdPlane x₀ P (j + 1) ∧
            (∀ z ∈ cdPlane x₀ P (j + 1), z ≠ y → (h - y) ⬝ᵥ (h - y) < (h - z) ⬝ᵥ (h - z)) ∧
            (∃ t : ℝ, 1 < t ∧ y = X j + t • (X (j + 1) - X j)) ∧
            1 / errorFun A h y = 1 / errorFun A h (X (j + 1)) - 1 / errorFun A h (X j) ∧
            (h - X (j + 1)) ⬝ᵥ (h - X (j + 1)) = (h - y) ⬝ᵥ (h - y) +
              (errorFun A h y - errorFun A h (X (j + 1))) / rayleigh A (P j) by
            exact key (fun i => (cgIter A k x₀ i).x) (fun i => (cgIter A k x₀ i).r)
              (fun i => (cgIter A k x₀ i).p) (fun i => cgAlpha A (cgIter A k x₀ i))
              (fun i => (cgIter A k x₀ (i+1)).r ⬝ᵥ (cgIter A k x₀ (i+1)).r /
                ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r))
              rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hact hm
          intro X R P α β hX0 hR0 hP0 hα hβ hX hRs hPs hact hRm y
          clear hm
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
          have hαpos : ∀ i < m, 0 < α i := by
            intro i hi
            have hr := hRRpos i hi
            have hp : P i ≠ 0 := by
              intro hp
              have := (hQ i).2
              rw [hp] at this; simp at this; linarith
            rw [hα]; exact div_pos hr (hpos _ hp)
          have hcpos : ∀ i < m, 0 < α i * (R i ⬝ᵥ R i) := fun i hi => mul_pos (hαpos i hi) (hRRpos i hi)
          have hsum : ∀ d, errorFun A h (X j) - errorFun A h (X (j+d)) =
              ∑ l ∈ Finset.range d, α (j+l) * (R (j+l) ⬝ᵥ R (j+l)) := by
            intro d
            induction d with
            | zero => simp
            | succ d ih =>
              rw [Finset.sum_range_succ, ← ih, ← hdec (j+d), ← add_assoc]
              ring
          have hXs : ∀ a d, X (a+d) = X a + ∑ l ∈ Finset.range d, α (a+l) • P (a+l) := by
            intro a d
            induction d with
            | zero => simp
            | succ d ih =>
              rw [Finset.sum_range_succ, ← add_assoc, hX, ih, add_assoc]
          have hRstay : ∀ i, R i = 0 → R (i+1) = 0 := by
            intro i hi; rw [hRs, hi, hRP0 i hi]; simp
          have hPP : ∀ i d, (R i ⬝ᵥ R i) * (P (i+d) ⬝ᵥ P i) = (R (i+d) ⬝ᵥ R (i+d)) * (P i ⬝ᵥ P i) := by
            intro i d
            induction d with
            | zero => simp
            | succ d ih =>
              have h1 : P (i+(d+1)) ⬝ᵥ P i = β (i+d) * (P (i+d) ⬝ᵥ P i) := by
                rw [← add_assoc, hPs, add_dotProduct, smul_dotProduct, ((hQ (i+d+1)).1 i (by omega)).1,
                  smul_eq_mul, zero_add]
              have h2 : β (i+d) * (R (i+d) ⬝ᵥ R (i+d)) = R (i+(d+1)) ⬝ᵥ R (i+(d+1)) := by
                by_cases hz : R (i+d) ⬝ᵥ R (i+d) = 0
                · have := hRstay _ (hzero _ hz)
                  rw [← add_assoc, this, hz]; simp
                · rw [hβ, ← add_assoc]; field_simp
              rw [h1, ← h2]
              linear_combination β (i+d) * ih
          have hsumg : ∀ a d, errorFun A h (X a) - errorFun A h (X (a+d)) =
              ∑ l ∈ Finset.range d, α (a+l) * (R (a+l) ⬝ᵥ R (a+l)) := by
            intro a d
            induction d with
            | zero => simp
            | succ d ih =>
              rw [Finset.sum_range_succ, ← ih, ← hdec (a+d), ← add_assoc]
              ring
          obtain ⟨d, rfl⟩ : ∃ d, m = j + 1 + d := ⟨m - (j+1), by omega⟩
          have hXm : X (j+1+d) = h := by
            have h1 := hAE (j+1+d)
            rw [hRm] at h1
            by_contra hne
            have := hpos (h - X (j+1+d)) (sub_ne_zero.mpr (Ne.symm hne))
            rw [h1] at this; simp at this
          have hfm : errorFun A h (X (j+1+d)) = 0 := by rw [hXm]; simp [errorFun]
          have hRj : 0 < R j ⬝ᵥ R j := hRRpos j (by omega)
          have hαj : 0 < α j := hαpos j (by omega)
          have hPj : P j ≠ 0 := by
            intro hp
            have := (hQ j).2
            rw [hp] at this; simp at this; linarith
          have hdpos : 0 < P j ⬝ᵥ (A *ᵥ P j) := hpos _ hPj
          have hqpos : 0 < P j ⬝ᵥ P j := by
            rcases (hself (P j)).lt_or_eq with h1 | h1
            · exact h1
            · exact absurd (hzero _ h1.symm) hPj
          have hF1pos : 0 < errorFun A h (X (j+1)) := by
            have hne : h - X (j+1) ≠ 0 := by
              intro h0
              have := hAE (j+1)
              rw [h0] at this; simp at this
              exact hact (j+1) (by omega) this.symm
            exact hpos _ hne
          have he1 : errorFun A h (X j) - errorFun A h (X (j+1)) = α j * (R j ⬝ᵥ R j) := hdec j
          have hαd : α j * (P j ⬝ᵥ (A *ᵥ P j)) = R j ⬝ᵥ R j := by
            rw [hα]; field_simp
          set F1 := errorFun A h (X (j+1)) with hF1
          set c := F1 / (R j ⬝ᵥ R j) with hcdef
          have hc : c * (R j ⬝ᵥ R j) = F1 := by rw [hcdef]; field_simp
          have hcpos' : 0 < c := div_pos hF1pos hRj
          have hS : F1 = ∑ l ∈ Finset.range d, α (j+1+l) * (R (j+1+l) ⬝ᵥ R (j+1+l)) := by
            have := hsumg (j+1) d
            rw [hfm, sub_zero] at this
            exact this
          have hyd : y = X (j+1) + c • P j := rfl
          have hort : ∀ i ≤ j, (h - y) ⬝ᵥ P i = 0 := by
            intro i hi
            have hRi : 0 < R i ⬝ᵥ R i := hRRpos i (by omega)
            have hmain : (R i ⬝ᵥ R i) * ((h - y) ⬝ᵥ P i) = 0 := by
              rw [hyd, ← hXm, hXs (j+1) d, show ∀ u v w : Fin n → ℝ, u + v - (u + w) = v - w from
                fun u v w => by abel, sub_dotProduct, sum_dotProduct, mul_sub, Finset.mul_sum]
              have h1 : ∀ l ∈ Finset.range d, (R i ⬝ᵥ R i) * ((α (j+1+l) • P (j+1+l)) ⬝ᵥ P i) =
                  α (j+1+l) * (R (j+1+l) ⬝ᵥ R (j+1+l)) * (P i ⬝ᵥ P i) := by
                intro l _
                have := hPP i (j + 1 + l - i)
                rw [show i + (j + 1 + l - i) = j + 1 + l by omega] at this
                rw [smul_dotProduct, smul_eq_mul]
                linear_combination α (j+1+l) * this
              rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← hS]
              have h2 := hPP i (j - i)
              rw [show i + (j - i) = j by omega] at h2
              rw [smul_dotProduct, smul_eq_mul]
              linear_combination (-c) * h2 - (P i ⬝ᵥ P i) * hc
            rcases mul_eq_zero.mp hmain with h | h
            · linarith
            · exact h
          have hz1 : P j ⬝ᵥ R (j+1) = 0 := by
            rw [dotProduct_comm]; exact ((hQ (j+1)).1 j (by omega)).1
          have hfy : errorFun A h y = F1 + c^2 * (P j ⬝ᵥ (A *ᵥ P j)) := by
            have e : h - y = (h - X (j+1)) - c • P j := by rw [hyd]; abel
            have hz2 : (h - X (j+1)) ⬝ᵥ (A *ᵥ P j) = 0 := by
              rw [hsym, hAE]; exact hz1
            rw [hF1]
            unfold errorFun
            rw [e]
            simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
              smul_dotProduct, dotProduct_smul, smul_eq_mul, hAE, hz1, hz2]
            ring
          have hymem : ∃ α' : ℕ → ℝ, y = x₀ + ∑ l ∈ Finset.range (j+1), α' l • P l := by
            have hXj : X j = x₀ + ∑ l ∈ Finset.range j, α l • P l := by
              have := hXs 0 j; simpa [hX0] using this
            let α' : ℕ → ℝ := fun l => if l < j then α l else α j + c
            refine ⟨α', ?_⟩
            rw [hyd, hX, Finset.sum_range_succ, hXj, add_assoc, add_assoc]
            congr 1
            have : ∑ l ∈ Finset.range j, α' l • P l = ∑ l ∈ Finset.range j, α l • P l := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [Finset.mem_range] at hl
              simp only [α', if_pos hl]
            rw [this]
            simp only [α', lt_irrefl, if_false, add_smul]
          refine ⟨hymem, ?_, ?_, ?_, ?_⟩
          · -- nearest point
            rintro z ⟨γ, rfl⟩ hne
            obtain ⟨α', hy'⟩ := hymem
            have hperp : (h - y) ⬝ᵥ (y - (x₀ + ∑ l ∈ Finset.range (j + 1), γ l • P l)) = 0 := by
              rw [hy', add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
              simp only [← sub_smul]
              rw [← hy', dotProduct_sum]
              apply Finset.sum_eq_zero
              intro l hl
              rw [Finset.mem_range] at hl
              rw [dotProduct_smul, hort l (by omega), smul_zero]
            set w := y - (x₀ + ∑ l ∈ Finset.range (j + 1), γ l • P l) with hw
            have hwne : w ≠ 0 := by
              rw [hw]; intro h0; exact hne (sub_eq_zero.mp h0).symm
            have hwpos : 0 < w ⬝ᵥ w := by
              rcases (hself w).lt_or_eq with h1 | h1
              · exact h1
              · exact absurd (hzero _ h1.symm) hwne
            have e : h - (x₀ + ∑ l ∈ Finset.range (j + 1), γ l • P l) = (h - y) + w := by
              rw [hw]; abel
            rw [e, add_dotProduct, dotProduct_add, dotProduct_add, hperp, dotProduct_comm w (h - y), hperp]
            linarith
          · refine ⟨1 + c / α j, by have := div_pos hcpos' hαj; linarith, ?_⟩
            rw [hyd, hX, show X j + α j • P j - X j = α j • P j by abel, smul_smul, add_assoc]
            congr 1
            rw [← add_smul]
            congr 1
            field_simp
          · have hF0 : errorFun A h (X j) = F1 + α j * (R j ⬝ᵥ R j) := by linarith
            have hF0pos : 0 < F1 + α j * (R j ⬝ᵥ R j) := by
              have := mul_pos hαj hRj; linarith
            have hfypos : 0 < F1 + c ^ 2 * (P j ⬝ᵥ (A *ᵥ P j)) := by
              have := mul_pos (pow_pos hcpos' 2) hdpos; linarith
            rw [hfy, hF0, div_sub_div _ _ hF1pos.ne' hF0pos.ne',
              div_eq_div_iff hfypos.ne' (mul_pos hF1pos hF0pos).ne']
            linear_combination (-(c * (R j ⬝ᵥ R j) + F1)) * hc - (c ^ 2 * (R j ⬝ᵥ R j)) * hαd
          · have e : h - X (j+1) = (h - y) + c • P j := by rw [hyd]; abel
            have ho := hort j le_rfl
            have ho' : P j ⬝ᵥ (h - y) = 0 := by rw [dotProduct_comm]; exact ho
            rw [hfy, e]
            unfold rayleigh
            simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
              ho, ho']
            field_simp
            ring
