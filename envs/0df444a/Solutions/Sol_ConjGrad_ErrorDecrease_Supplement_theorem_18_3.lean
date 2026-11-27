-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_18_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:48.266259+00:00
-- url     : https://prove2.me/submissions/6d1efa1a-92da-4f3e-be20-c8b32375792f

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 18:3 (Hestenes–Stiefel 1952, p. 432): any positive numbers `a₀, …, aₙ₋₁` and
`b₀, …, bₙ₋₁` are the first `n` step lengths and coefficients of the cg-algorithm for some
symmetric positive definite matrix `A` (here of order `n + 1`) and initial residual. -/
theorem solution (n : ℕ) (a b : ℕ → ℝ) (ha : ∀ i < n, 0 < a i) (hb : ∀ i < n, 0 < b i) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, A.PosDef ∧ ∃ k x₀ : Fin (n + 1) → ℝ,
      ∀ i < n, cgAlpha A (cgIter A k x₀ i) = a i ∧ cgBeta A k x₀ i = b i := by
        classical
        obtain ⟨a', ha'⟩ : ∃ a' : ℕ → ℝ, a' = fun j => if j < n then a j else 1 := ⟨_, rfl⟩
        obtain ⟨b', hb'⟩ : ∃ b' : ℕ → ℝ, b' = fun j => if j < n then b j else 1 := ⟨_, rfl⟩
        have ha'pos : ∀ j, 0 < a' j := fun j => by
          rw [ha']; dsimp only; split_ifs with h
          · exact ha j h
          · norm_num
        have hb'pos : ∀ j, 0 < b' j := fun j => by
          rw [hb']; dsimp only; split_ifs with h
          · exact hb j h
          · norm_num
        obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, s = fun j => Real.sqrt (b' j) := ⟨_, rfl⟩
        have hspos : ∀ j, 0 < s j := fun j => by rw [hs]; exact Real.sqrt_pos.2 (hb'pos j)
        have hs2 : ∀ j, s j * s j = b' j := fun j => by rw [hs]; exact Real.mul_self_sqrt (hb'pos j).le
        obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ρ = fun i => ∏ j ∈ Finset.range i, s j := ⟨_, rfl⟩
        have hρpos : ∀ i, 0 < ρ i := fun i => by
          rw [hρ]; exact Finset.prod_pos (fun j _ => hspos j)
        have hρsucc : ∀ i, ρ (i+1) = ρ i * s i := fun i => by
          rw [hρ]; exact Finset.prod_range_succ _ _
        have hρ0 : ρ 0 = 1 := by rw [hρ]; exact Finset.prod_range_zero _
        obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,
            N = Matrix.of fun (j l : Fin (n+1)) => if (l:ℕ) = (j:ℕ) + 1 then s j else 0 := ⟨_, rfl⟩
        obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, M = 1 - N := ⟨_, rfl⟩
        obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,
            D = Matrix.diagonal fun (l : Fin (n+1)) => 1 / a' l := ⟨_, rfl⟩
        obtain ⟨R, hR⟩ : ∃ R : ℕ → Fin (n+1) → ℝ, R = fun i (l : Fin (n+1)) => if (l:ℕ) = i then ρ i else 0 :=
          ⟨_, rfl⟩
        obtain ⟨P, hP⟩ : ∃ P : ℕ → Fin (n+1) → ℝ,
            P = fun i (l : Fin (n+1)) => if (l:ℕ) ≤ i then ρ i ^ 2 / ρ l else 0 := ⟨_, rfl⟩
        have hMinj : Function.Injective M.mulVec := by
          rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
          have : M.det = 1 := by
            rw [Matrix.det_of_isUpperTriangular]
            · apply Finset.prod_eq_one
              intro i _
              simp [hM, hN]
            · intro i j hij
              have h1 : (j:ℕ) < i := hij
              have h2 : i ≠ j := fun h => by subst h; exact lt_irrefl _ h1
              simp only [hM, hN, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, if_neg h2]
              rw [if_neg (by omega)]; simp
          simp [this]
        have hApd : (Mᴴ * D * M).PosDef := by
          have hDpd : D.PosDef := by
            rw [hD]; exact Matrix.PosDef.diagonal (fun l => one_div_pos.2 (ha'pos l))
          exact hDpd.conjTranspose_mul_mul_same hMinj
        have hdot : ∀ i (hi : i ≤ n), ∀ v : Fin (n+1) → ℝ, R i ⬝ᵥ v = ρ i * v ⟨i, Nat.lt_succ_of_le hi⟩ := by
          intro i hi v
          rw [dotProduct, Finset.sum_eq_single (⟨i, by omega⟩ : Fin (n+1))]
          · simp [hR]
          · intro l _ hl
            have : (l:ℕ) ≠ i := fun h => hl (Fin.ext h)
            simp [hR, this]
          · simp
        have hNv : ∀ (v : Fin (n+1) → ℝ) (j : Fin (n+1)),
            (N *ᵥ v) j = if h : (j:ℕ) + 1 ≤ n then s j * v ⟨j+1, by omega⟩ else 0 := by
          intro v j
          rw [Matrix.mulVec, dotProduct]
          split_ifs with h
          · rw [Finset.sum_eq_single (⟨j+1, by omega⟩ : Fin (n+1))]
            · simp [hN]
            · intro l _ hl
              have : (l:ℕ) ≠ j + 1 := fun h => hl (Fin.ext h)
              simp [hN, this]
            · simp
          · apply Finset.sum_eq_zero
            intro l _
            have : (l:ℕ) ≠ j + 1 := by have := l.isLt; omega
            simp [hN, this]
        have hMP : ∀ i ≤ n, M *ᵥ P i = R i := by
          intro i hi
          funext j
          rw [hM, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, hNv]
          have hj := j.isLt
          have := hρpos j; have := hspos j; have := hρpos i
          simp only [hP, hR, Fin.val_mk]
          split_ifs <;> first | (exfalso; omega) | skip
          all_goals first | ring1 | (subst_vars; field_simp; ring1) | (rw [hρsucc]; field_simp; ring1) | (subst_vars; field_simp)
        have hMtR : ∀ i < n, Mᴴ *ᵥ R i = R i - R (i+1) := by
          intro i hi
          funext l
          rw [Matrix.mulVec, dotProduct_comm, hdot i (by omega)]
          simp only [Matrix.conjTranspose_apply, star_trivial, hM, hN, Matrix.sub_apply,
            Matrix.one_apply, Matrix.of_apply, Pi.sub_apply, hR, Fin.ext_iff, Fin.val_mk]
          have hl := l.isLt
          split_ifs <;> first | (exfalso; omega) | skip
          all_goals first | ring1 | (rw [hρsucc]; ring1)
        have hDR : ∀ i, D *ᵥ R i = (1 / a' i) • R i := by
          intro i; funext l
          rw [hD, Matrix.mulVec_diagonal, Pi.smul_apply, hR]
          dsimp only
          split_ifs with h
          · rw [h]; simp
          · simp
        have hAP : ∀ i < n, (Mᴴ * D * M) *ᵥ P i = (1 / a' i) • (R i - R (i+1)) := by
          intro i hi
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMP i hi.le, hDR, Matrix.mulVec_smul,
            hMtR i hi]
        have hRR : ∀ i ≤ n, R i ⬝ᵥ R i = ρ i * ρ i := by
          intro i hi; rw [hdot i hi]; simp [hR]
        refine ⟨Mᴴ * D * M, hApd, R 0, 0, ?_⟩
        set A := Mᴴ * D * M with hA
        have hr_succ : ∀ i, (cgIter A (R 0) 0 (i+1)).r = (cgIter A (R 0) 0 i).r -
            cgAlpha A (cgIter A (R 0) 0 i) • (A *ᵥ (cgIter A (R 0) 0 i).p) := fun i => rfl
        have hp_succ : ∀ i, (cgIter A (R 0) 0 (i+1)).p = (cgIter A (R 0) 0 (i+1)).r +
            (((cgIter A (R 0) 0 (i+1)).r ⬝ᵥ (cgIter A (R 0) 0 (i+1)).r) /
              ((cgIter A (R 0) 0 i).r ⬝ᵥ (cgIter A (R 0) 0 i).r)) • (cgIter A (R 0) 0 i).p :=
          fun i => rfl
        have hα : ∀ i < n, (cgIter A (R 0) 0 i).r = R i → (cgIter A (R 0) 0 i).p = P i →
            cgAlpha A (cgIter A (R 0) 0 i) = a' i := by
          intro i hi h1 h2
          unfold cgAlpha
          rw [h1, h2, hAP i hi, hRR i hi.le, dotProduct_smul, dotProduct_sub, dotProduct_comm,
            hdot i hi.le, dotProduct_comm, hdot (i+1) hi]
          simp only [hP, smul_eq_mul]
          rw [if_pos le_rfl, if_neg (by simp)]
          have := hρpos i; have := ha'pos i
          field_simp
          try ring
        have main : ∀ i ≤ n, (cgIter A (R 0) 0 i).r = R i ∧ (cgIter A (R 0) 0 i).p = P i := by
          intro i
          induction i with
          | zero =>
            intro _
            have hr0 : (cgIter A (R 0) 0 0).r = R 0 := by simp [cgIter]
            refine ⟨hr0, ?_⟩
            have : (cgIter A (R 0) 0 0).p = (cgIter A (R 0) 0 0).r := rfl
            rw [this, hr0]
            funext l
            simp only [hR, hP, Nat.le_zero]
            split_ifs with h
            · rw [h, hρ0]; norm_num
            · rfl
          | succ i ih =>
            intro hi
            have ih' := ih (by omega)
            have hri : (cgIter A (R 0) 0 (i+1)).r = R (i+1) := by
              rw [hr_succ, hα i (by omega) ih'.1 ih'.2, ih'.1, ih'.2, hAP i (by omega), smul_smul,
                mul_one_div_cancel (ha'pos i).ne', one_smul, sub_sub_cancel]
            refine ⟨hri, ?_⟩
            rw [hp_succ, hri, ih'.1, ih'.2, hRR _ hi, hRR _ (by omega), hρsucc]
            funext l
            have hl := l.isLt
            simp only [hP, hR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have := hρpos i; have := hspos i
            by_cases h1 : (l:ℕ) ≤ i
            · rw [if_neg (by omega), if_pos h1, if_pos (by omega), hρsucc]
              field_simp
              try ring
            · by_cases h2 : (l:ℕ) = i + 1
              · rw [if_pos h2, if_neg h1, if_pos (by omega), h2, hρsucc]
                field_simp
                try ring
              · rw [if_neg h2, if_neg h1, if_neg (by omega)]; ring
        intro i hi
        have m1 := main i hi.le
        have m2 := main (i+1) hi
        refine ⟨?_, ?_⟩
        · rw [hα i hi m1.1 m1.2, ha']; simp [hi]
        · unfold cgBeta
          rw [m2.1, m1.1, hRR _ hi, hRR _ hi.le, hρsucc]
          have := hρpos i
          have hb2 : b' i = b i := by rw [hb']; simp [hi]
          rw [← hb2, ← hs2]
          field_simp
