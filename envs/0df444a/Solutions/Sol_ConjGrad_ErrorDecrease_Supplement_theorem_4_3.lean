-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:46.367799+00:00
-- url     : https://prove2.me/submissions/015b7561-1274-41b3-8957-d62f9c1a7f59

import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 4:3 (Hestenes–Stiefel 1952, p. 413), for every run of the cd-method; the paper's
step `i` is the Lean step `i + 1`. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) (x r p : ℕ → Fin n → ℝ)
    (hcd : Termination.IsCDRun A k x r p) :
    (∀ (i : ℕ) (α : ℝ), errorFun A h (x (i + 1)) ≤ errorFun A h (x i + α • p i)) ∧
    (∀ i : ℕ, errorFun A h (x i) - errorFun A h (x (i + 1)) =
        (p i ⬝ᵥ r i) ^ 2 / (p i ⬝ᵥ (A *ᵥ p i))) ∧
    (∀ i : ℕ, x i ∈ cdPlane (x 0) p i ∧
        ∀ y ∈ cdPlane (x 0) p i, errorFun A h (x i) ≤ errorFun A h y) ∧
    (∀ i : ℕ, ∀ j ≤ i, x j ∈ cdPlane (x 0) p i) ∧
    (∀ i : ℕ, (∀ j < i, p j ≠ 0) → LinearIndependent ℝ (fun j : Fin i => p j)) := by
      classical
      have hAt : Aᵀ = A := by simpa using hA.isHermitian.eq
      have hsym (u v : Fin n → ℝ) : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
        rw [← hAt, dotProduct_transpose_mulVec, hAt]
      have hpos (u : Fin n → ℝ) (hu : u ≠ 0) : 0 < u ⬝ᵥ (A *ᵥ u) := by
        simpa using hA.dotProduct_mulVec_pos hu
      have hnonneg (u : Fin n → ℝ) : 0 ≤ u ⬝ᵥ (A *ᵥ u) := by
        simpa using hA.posSemidef.dotProduct_mulVec_nonneg u
      have hr (i : ℕ) : A *ᵥ (h - x i) = r i := by
        rw [mulVec_sub, hh, hcd.residual]
      have hexp (z v : Fin n → ℝ) :
          errorFun A h (z + v) = errorFun A h z -
            2 * (v ⬝ᵥ (A *ᵥ (h - z))) + v ⬝ᵥ (A *ᵥ v) := by
        have hv : h - (z + v) = (h - z) - v := by abel
        simp only [errorFun, hv, mulVec_sub, sub_dotProduct, dotProduct_sub]
        rw [hsym h v, hsym z v]
        ring
      have hline (i : ℕ) (a : ℝ) :
          errorFun A h (x i + a • p i) = errorFun A h (x i) -
            2 * a * (p i ⬝ᵥ r i) + a ^ 2 * (p i ⬝ᵥ (A *ᵥ p i)) := by
        rw [hexp, hr]
        simp only [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul]
        ring
      have hconj (i j : ℕ) (hij : i ≠ j) : p i ⬝ᵥ (A *ᵥ p j) = 0 := by
        rcases lt_or_gt_of_ne hij with hij | hij
        · rw [hsym]
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_le i |>.trans_lt hij))
          exact hcd.conj j i (by omega)
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_le j |>.trans_lt hij))
          exact hcd.conj i j (by omega)
      have hresstep (i : ℕ) : r (i + 1) = r i -
          ((p i ⬝ᵥ r i) / (p i ⬝ᵥ (A *ᵥ p i))) • (A *ᵥ p i) := by
        rw [hcd.residual (i + 1), hcd.step, mulVec_add, mulVec_smul, hcd.residual i]
        abel
      have horth (i j : ℕ) (hji : j < i) : p j ⬝ᵥ r i = 0 := by
        induction i with
        | zero => omega
        | succ i ih =>
          rw [hresstep, dotProduct_sub, dotProduct_smul, smul_eq_mul]
          by_cases hji' : j = i
          · subst j
            by_cases hp : p i = 0
            · simp [hp]
            · have hq := ne_of_gt (hpos (p i) hp)
              field_simp
              ring
          · rw [ih (by omega), hconj j i hji']
            ring
      let a : ℕ → ℝ := fun i => (p i ⬝ᵥ r i) / (p i ⬝ᵥ (A *ᵥ p i))
      have hstep (i : ℕ) : x (i + 1) = x i + a i • p i := hcd.step i
      have hdec (i : ℕ) : errorFun A h (x i) - errorFun A h (x (i + 1)) =
          (p i ⬝ᵥ r i) ^ 2 / (p i ⬝ᵥ (A *ᵥ p i)) := by
        rw [hstep, hline]
        by_cases hp : p i = 0
        · simp [hp]
        · have hq := ne_of_gt (hpos (p i) hp)
          dsimp [a]
          field_simp
          ring
      have hmin (i : ℕ) (α : ℝ) :
          errorFun A h (x (i + 1)) ≤ errorFun A h (x i + α • p i) := by
        by_cases hp : p i = 0
        · simp [hstep, hp]
        · have hq := hpos (p i) hp
          have heq : errorFun A h (x i + α • p i) - errorFun A h (x (i + 1)) =
              (α - a i) ^ 2 * (p i ⬝ᵥ (A *ᵥ p i)) := by
            rw [hstep, hline, hline]
            dsimp [a]
            field_simp
            ring
          have := mul_nonneg (sq_nonneg (α - a i)) (le_of_lt hq)
          linarith
      have hx (i : ℕ) : x i = x 0 + ∑ j ∈ Finset.range i, a j • p j := by
        induction i with
        | zero => simp
        | succ i ih => rw [hstep, ih, Finset.sum_range_succ, add_assoc]
      have hmem (i j : ℕ) (hji : j ≤ i) : x j ∈ cdPlane (x 0) p i := by
        refine ⟨fun l => if l < j then a l else 0, ?_⟩
        rw [hx j]
        congr 1
        have heq : (∑ l ∈ Finset.range j, (if l < j then a l else 0) • p l) =
            ∑ l ∈ Finset.range i, (if l < j then a l else 0) • p l := by
          apply Finset.sum_subset (Finset.range_mono hji)
          intro l hli hlj
          simp only [Finset.mem_range, not_lt] at hlj
          simp [not_lt.mpr hlj]
        rw [← heq]
        apply Finset.sum_congr rfl
        intro l hl
        simp [Finset.mem_range.mp hl]
      have hplane (i : ℕ) (y : Fin n → ℝ) (hy : y ∈ cdPlane (x 0) p i) :
          errorFun A h (x i) ≤ errorFun A h y := by
        obtain ⟨b, hb⟩ := hy
        let v : Fin n → ℝ := ∑ j ∈ Finset.range i, (b j - a j) • p j
        have hyv : y = x i + v := by
          rw [hb, hx i]
          dsimp [v]
          simp only [sub_smul, Finset.sum_sub_distrib]
          abel
        have hvorth : v ⬝ᵥ (A *ᵥ (h - x i)) = 0 := by
          rw [hr]
          dsimp [v]
          rw [sum_dotProduct]
          apply Finset.sum_eq_zero
          intro j hj
          rw [smul_dotProduct, horth i j (Finset.mem_range.mp hj)]
          simp
        rw [hyv, hexp, hvorth]
        have := hnonneg v
        linarith
      refine ⟨hmin, hdec, fun i => ⟨hmem i i le_rfl, hplane i⟩, hmem, ?_⟩
      intro i hp
      apply Fintype.linearIndependent_iff.mpr
      intro g hg j
      have heq := congrArg (fun u : Fin n → ℝ => u ⬝ᵥ (A *ᵥ p j)) hg
      rw [sum_dotProduct, zero_dotProduct] at heq
      have hsum : (∑ l : Fin i, g l • p l ⬝ᵥ (A *ᵥ p j)) =
          g j * (p j ⬝ᵥ (A *ᵥ p j)) := by
        rw [Finset.sum_eq_single j]
        · simp [smul_dotProduct, smul_eq_mul]
        · intro l hl hlj
          rw [smul_dotProduct, hconj l j (fun he => hlj (Fin.ext he))]
          simp
        · simp
      rw [hsum] at heq
      exact (mul_eq_zero.mp heq).resolve_right (ne_of_gt (hpos (p j) (hp j j.isLt)))
