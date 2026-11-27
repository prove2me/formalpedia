-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_7_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:33.029799+00:00
-- url     : https://prove2.me/submissions/36753c10-c716-432e-994b-1e686df48e60

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

open ConjGrad
open ConjGrad.ErrorDecrease
open ConjGrad.ErrorDecrease.Supplement

/-- Theorem 7:4 (Hestenes–Stiefel 1952, p. 419): the identity (7:7) for every `i`, the
inequalities (7:8) `f(xᵢ) < f(x̄ᵢ) < f(x̄ᵢ₋₁)` for `0 < i < m`, strict decrease of `f(x̄ᵢ)` through
the termination step `m`, monotone decrease of the whole sequence, and the endpoint equalities
`x̄₀ = x₀`, `x̄ₘ = xₘ`. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ, errorFun A h (smoothX A k x₀ i) = errorFun A h (cgIter A k x₀ i).x +
      ((k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i)) ^ 2 *
        ∑ j ∈ Finset.range i,
          (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ (j + 1)).x) /
            ((k - A *ᵥ smoothX A k x₀ j) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ j)) ^ 2) ∧
    (∀ i : ℕ, 0 < i → i < m →
      errorFun A h (cgIter A k x₀ i).x < errorFun A h (smoothX A k x₀ i)) ∧
    (∀ i : ℕ, i + 1 ≤ m →
      errorFun A h (smoothX A k x₀ (i + 1)) < errorFun A h (smoothX A k x₀ i)) ∧
    (∀ i : ℕ, errorFun A h (smoothX A k x₀ (i + 1)) ≤ errorFun A h (smoothX A k x₀ i)) ∧
    smoothX A k x₀ 0 = x₀ ∧ smoothX A k x₀ m = (cgIter A k x₀ m).x := by
      classical
      let x := fun i => (cgIter A k x₀ i).x
      let r := fun i => (cgIter A k x₀ i).r
      let p := fun i => (cgIter A k x₀ i).p
      let a := fun i => cgAlpha A (cgIter A k x₀ i)
      let b := cgBeta A k x₀
      let c := smoothC A k x₀
      let y := smoothX A k x₀
      let R := fun i => r i ⬝ᵥ r i
      let D := fun i => p i ⬝ᵥ (A *ᵥ p i)
      have nn (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v := by
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
      have pos (v : Fin n → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
        lt_of_le_of_ne (nn v) (Ne.symm (mt dotProduct_self_eq_zero.mp hv))
      have sym (u v : Fin n → ℝ) : u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
        have ht : Aᵀ = A := by simpa [Matrix.IsHermitian] using hA.isHermitian
        rw [dotProduct_mulVec, ← ht, vecMul_transpose, dotProduct_comm]
        rw [ht]
      have xstep (i) : x (i+1) = x i + a i • p i := rfl
      have rstep (i) : r (i+1) = r i - a i • (A *ᵥ p i) := rfl
      have pstep (i) : p (i+1) = r (i+1) + b i • p i := rfl
      have adef (i) : a i = R i / D i := rfl
      have bdef (i) : b i = R (i+1) / R i := rfl
      have rzero : r 0 = p 0 := rfl
      have residual (i) : r i = k - A *ᵥ x i := by
        induction i with
        | zero => rfl
        | succ i ih =>
          rw [rstep, xstep, mulVec_add, mulVec_smul, ih]
          module
      have invariants : ∀ i, i ≤ m →
          (r i ⬝ᵥ p i = R i) ∧
          (∀ j < i, r i ⬝ᵥ p j = 0) ∧
          (∀ j < i, r i ⬝ᵥ r j = 0) ∧
          (∀ j < i, p i ⬝ᵥ (A *ᵥ p j) = 0) := by
        intro i
        induction i using Nat.strong_induction_on with
        | h i ih =>
          intro him
          cases i with
          | zero => simp only [rzero]; exact ⟨rfl, by omega, by omega, by omega⟩
          | succ i =>
            have hi : i < m := by omega
            obtain ⟨hrp, hrpold, hrrold, hppold⟩ := ih i (by omega) (by omega)
            have hR : 0 < R i := pos (r i) (hact i hi)
            have hp : p i ≠ 0 := by
              intro hp
              have : R i = 0 := by rw [← hrp, hp, dotProduct_zero]
              linarith
            have hD : 0 < D i := by simpa [D] using hA.dotProduct_mulVec_pos hp
            have ha : a i * D i = R i := by rw [adef]; exact div_mul_cancel₀ _ (ne_of_gt hD)
            have hnpo : ∀ j ≤ i, r (i+1) ⬝ᵥ p j = 0 := by
              intro j hj
              rw [rstep, sub_dotProduct, smul_dotProduct]
              simp only [smul_eq_mul]
              by_cases hji : j = i
              · subst j
                rw [hrp, dotProduct_comm (A *ᵥ p i) (p i)]
                change R i - a i * D i = 0
                linarith
              · rw [hrpold j (by omega), dotProduct_comm (A *ᵥ p i) (p j),
                    ← sym, hppold j (by omega)]
                ring
            have hnro : ∀ j ≤ i, r (i+1) ⬝ᵥ r j = 0 := by
              intro j hj
              cases j with
              | zero => rw [rzero]; exact hnpo 0 (by omega)
              | succ j =>
                have he : r (j+1) = p (j+1) - b j • p j := by rw [pstep]; module
                rw [he, dotProduct_sub, dotProduct_smul, hnpo (j+1) hj, hnpo j (by omega)]
                simp
            have hnconj : ∀ j ≤ i, p (i+1) ⬝ᵥ (A *ᵥ p j) = 0 := by
              intro j hj
              rw [pstep, add_dotProduct, smul_dotProduct]
              simp only [smul_eq_mul]
              have eqr : a j * (r (i+1) ⬝ᵥ (A *ᵥ p j)) =
                  r (i+1) ⬝ᵥ r j - r (i+1) ⬝ᵥ r (j+1) := by
                rw [rstep j, dotProduct_sub, dotProduct_smul]
                simp only [smul_eq_mul]
                ring
              by_cases hji : j = i
              · subst j
                rw [hnro i (by omega)] at eqr
                change a i * (r (i+1) ⬝ᵥ (A *ᵥ p i)) = 0 - R (i+1) at eqr
                change r (i+1) ⬝ᵥ (A *ᵥ p i) + b i * D i = 0
                rw [bdef]
                rw [adef] at eqr
                field_simp [ne_of_gt hD] at eqr
                field_simp [ne_of_gt hR]
                nlinarith only [eqr]
              · have hjlt : j < i := by omega
                rw [hnro j hj, hnro (j+1) (by omega)] at eqr
                have hjR : 0 < R j := pos (r j) (hact j (by omega))
                obtain ⟨hjrp, _, _, _⟩ := ih j (by omega) (by omega)
                have hjp : p j ≠ 0 := by
                  intro hz
                  rw [hz, dotProduct_zero] at hjrp
                  linarith
                have hjD : 0 < D j := by simpa [D] using hA.dotProduct_mulVec_pos hjp
                have haj : a j ≠ 0 := by rw [adef]; exact div_ne_zero (ne_of_gt hjR) (ne_of_gt hjD)
                have hz : r (i+1) ⬝ᵥ (A *ᵥ p j) = 0 := by
                  apply (mul_eq_zero.mp (by simpa only [sub_self] using eqr)).resolve_left haj
                rw [hz, hppold j hjlt]; ring
            refine ⟨?_, fun j hj => hnpo j (by omega), fun j hj => hnro j (by omega),
              fun j hj => hnconj j (by omega)⟩
            rw [pstep, dotProduct_add, dotProduct_smul, hnpo i (by omega)]
            simp [R]
      have azero (i) (hz : r i = 0) : a i = 0 := by
        change (r i ⬝ᵥ r i) / D i = 0
        simp [hz]
      have stopped : ∀ i, m ≤ i → r i = 0 ∧ x i = x m := by
        intro i hi
        induction i, hi using Nat.le_induction with
        | base => exact ⟨hm, rfl⟩
        | succ i hi ih =>
          rw [rstep, xstep, azero i ih.1]
          simpa [ih.1, ih.2]
      have pstop (i) (hi : m ≤ i) : p i = 0 := by
        cases i with
        | zero => rw [← rzero]; exact (stopped 0 hi).1
        | succ i =>
          rw [pstep]
          have hr := (stopped (i+1) hi).1
          have hb : b i = 0 := by rw [bdef]; simp [R, hr]
          simp [hr, hb]
      have rp (i) : r i ⬝ᵥ p i = R i := by
        by_cases hi : i ≤ m
        · exact (invariants i hi).1
        · simp [R, (stopped i (by omega)).1]
      have rop (i j) (hj : j < i) : r i ⬝ᵥ p j = 0 := by
        by_cases hi : i ≤ m
        · exact (invariants i hi).2.1 j hj
        · simp [(stopped i (by omega)).1]
      have rpos (i) (hi : i < m) : 0 < R i := pos (r i) (hact i hi)
      have dpos (i) (hi : i < m) : 0 < D i := by
        have hp : p i ≠ 0 := by
          intro hz
          have := rp i
          rw [hz, dotProduct_zero] at this
          linarith [rpos i hi]
        simpa [D] using hA.dotProduct_mulVec_pos hp
      have bnn (i) : 0 ≤ b i := div_nonneg (nn _) (nn _)
      have bmul (i) : b i * R i = R (i+1) := by
        by_cases hi : i < m
        · rw [bdef, div_mul_cancel₀ _ (ne_of_gt (rpos i hi))]
        · have hr := (stopped i (by omega)).1
          have hrn := (stopped (i+1) (by omega)).1
          simp [R, hr, hrn]
      have cstep (i) : c (i+1) = 1 + b i * c i := rfl
      have ystep (i) : y (i+1) = (c (i+1))⁻¹ • (x (i+1) + (b i * c i) • y i) := rfl
      have cone (i) : 1 ≤ c i := by
        induction i with
        | zero => exact le_refl _
        | succ i ih => rw [cstep]; nlinarith only [bnn i, ih]
      have cpos (i) : 0 < c i := lt_of_lt_of_le zero_lt_one (cone i)
      have cne (i) : c i ≠ 0 := ne_of_gt (cpos i)
      have yscale (i) : c (i+1) • y (i+1) = x (i+1) + (b i * c i) • y i := by
        rw [ystep, smul_smul, mul_inv_cancel₀ (cne (i+1)), one_smul]
      have psmooth (i) : p i = c i • (k - A *ᵥ y i) := by
        induction i with
        | zero => simp [p, c, y, smoothC, smoothX, smoothed, cgIter]
        | succ i ih =>
          have hy := congrArg (fun v => A *ᵥ v) (yscale i)
          simp only [mulVec_smul, mulVec_add] at hy
          rw [pstep, ih, residual]
          rw [cstep] at hy ⊢
          linear_combination (norm := module) hy
      have pnorm (i) : p i ⬝ᵥ p i = c i * R i := by
        induction i with
        | zero => simp [← rzero, c, smoothC, smoothed, R]
        | succ i ih =>
          have hn := rop (i+1) i (by omega)
          rw [pstep, add_dotProduct, dotProduct_add, dotProduct_add,
            smul_dotProduct, dotProduct_smul, smul_dotProduct, dotProduct_smul,
            hn, dotProduct_comm (p i) (r (i+1)), hn, ih, cstep]
          simp only [smul_eq_mul]
          change R (i+1) + b i * 0 + (b i * 0 + b i * (b i * (c i * R i))) = _
          linear_combination b i * c i * bmul i
      let S := fun i => (k - A *ᵥ y i) ⬝ᵥ (k - A *ᵥ y i)
      have snorm (i) : S i = R i / c i := by
        have hp := pnorm i
        rw [psmooth i, smul_dotProduct, dotProduct_smul] at hp
        change c i * (c i * S i) = c i * R i at hp
        have hp' := (mul_left_cancel₀ (cne i)) hp
        apply (eq_div_iff (cne i)).2
        nlinarith only [hp']
      have spos (i) (hi : i < m) : 0 < S i := by rw [snorm]; exact div_pos (rpos i hi) (cpos i)
      have xspan (i j) (hj : j ≤ i) : r i ⬝ᵥ (x j - x₀) = 0 := by
        induction j with
        | zero => simp [x, cgIter]
        | succ j ih =>
          rw [xstep, add_sub_right_comm, dotProduct_add, dotProduct_smul,
            ih (by omega), rop i j (by omega)]
          simp
      have yspan (i j) (hj : j ≤ i) : r i ⬝ᵥ (y j - x₀) = 0 := by
        induction j with
        | zero => simp [y, smoothX, smoothed]
        | succ j ih =>
          have hh' : c (j+1) • (y (j+1) - x₀) =
              (x (j+1) - x₀) + (b j * c j) • (y j - x₀) := by
            rw [smul_sub, yscale, cstep]
            module
          have he := congrArg (fun v => r i ⬝ᵥ v) hh'
          rw [dotProduct_smul, dotProduct_add, dotProduct_smul, xspan i (j+1) hj,
            ih (by omega)] at he
          simp only [smul_eq_mul, mul_zero, zero_add] at he
          exact (mul_eq_zero.mp he).resolve_left (cne (j+1))
      have orth (i j) (hj : j ≤ i) : r i ⬝ᵥ (y j - x i) = 0 := by
        have he : y j - x i = (y j - x₀) - (x i - x₀) := by module
        rw [he, dotProduct_sub, yspan i j hj, xspan i i (le_refl _)]
        ring
      let Q := fun v : Fin n → ℝ => v ⬝ᵥ (A *ᵥ v)
      let F := errorFun A h
      have qsmul (t : ℝ) (v : Fin n → ℝ) : Q (t • v) = t^2 * Q v := by
        simp only [Q, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        ring
      have qsub (u v : Fin n → ℝ) : Q (u-v) = Q u - 2 * (u ⬝ᵥ (A *ᵥ v)) + Q v := by
        simp only [Q, mulVec_sub, sub_dotProduct, dotProduct_sub]
        rw [sym v u]
        ring
      have fshift (v d : Fin n → ℝ) :
          F (v+d) = F v - 2 * ((k - A *ᵥ v) ⬝ᵥ d) + Q d := by
        have he : h - (v+d) = (h-v) - d := by module
        have hr : A *ᵥ (h-v) = k - A *ᵥ v := by rw [mulVec_sub, hh]
        change Q (h - (v+d)) = Q (h-v) - 2 * ((k - A *ᵥ v) ⬝ᵥ d) + Q d
        rw [he, qsub, sym (h-v) d, hr, dotProduct_comm d (k - A *ᵥ v)]
      have amul (i) : a i * D i = R i := by
        by_cases hi : i < m
        · rw [adef, div_mul_cancel₀ _ (ne_of_gt (dpos i hi))]
        · have hr := (stopped i (by omega)).1
          simp [azero i hr, R, hr]
      have drop (i) : F (x i) - F (x (i+1)) = a i * R i := by
        rw [xstep, fshift, ← residual, dotProduct_smul, qsmul, rp]
        change F (x i) - (F (x i) - 2 * (a i * R i) + a i ^ 2 * D i) = _
        linear_combination -a i * amul i
      have droppos (i) (hi : i < m) : 0 < F (x i) - F (x (i+1)) := by
        rw [drop, adef]
        exact mul_pos (div_pos (rpos i hi) (dpos i hi)) (rpos i hi)
      have dropnn (i) : 0 ≤ F (x i) - F (x (i+1)) := by
        by_cases hi : i < m
        · exact le_of_lt (droppos i hi)
        · have hr := (stopped i (by omega)).1
          rw [drop, azero i hr, zero_mul]
      have pyth (i j) (hj : j ≤ i) (t : ℝ) :
          F (x i + t • (y j - x i)) = F (x i) + t^2 * Q (y j - x i) := by
        rw [fshift, ← residual, dotProduct_smul, orth i j hj, qsmul]
        simp
      let w := fun i => (b i * c i) / c (i+1)
      have ynext (i) : y (i+1) = x (i+1) + w i • (y i - x (i+1)) := by
        apply (smul_right_injective _ (cne (i+1)))
        dsimp only
        rw [yscale]
        simp only [smul_add, smul_smul, smul_sub]
        have hw : c (i+1) * w i = b i * c i := by
          dsimp [w]
          field_simp [cne (i+1)]
        rw [hw, cstep]
        module
      have frec (i) : F (y (i+1)) = F (x (i+1)) +
          (w i)^2 * (F (y i) - F (x (i+1))) := by
        have he := pyth (i+1) i (by omega) 1
        simp only [one_smul, add_sub_cancel, one_pow, one_mul] at he
        rw [ynext, pyth (i+1) i (by omega) (w i)]
        rw [he]
        ring
      have wnn (i) : 0 ≤ w i := div_nonneg (mul_nonneg (bnn i) (le_of_lt (cpos i))) (le_of_lt (cpos (i+1)))
      have wlt (i) : w i < 1 := by
        apply (div_lt_one (cpos (i+1))).2
        rw [cstep]
        linarith
      have wpos (i) (hi : i+1 < m) : 0 < w i := by
        have hb : 0 < b i := by rw [bdef]; exact div_pos (rpos (i+1) hi) (rpos i (by omega))
        exact div_pos (mul_pos hb (cpos i)) (cpos (i+1))
      have wratio (i) (hi : i < m) : w i = S (i+1) / S i := by
        dsimp [w]
        rw [snorm, snorm, bdef]
        field_simp [ne_of_gt (rpos i hi), cne i, cne (i+1)]
      have ystop (i) (hi : m ≤ i) : y i = x i := by
        cases i with
        | zero => rfl
        | succ i =>
          have hr := (stopped (i+1) hi).1
          have hb : b i = 0 := by rw [bdef]; simp [R, hr]
          rw [ystep, cstep, hb]
          simp
      have szero (i) (hi : m ≤ i) : S i = 0 := by
        rw [snorm]
        simp [R, (stopped i hi).1]
      have gapnn (i) : 0 ≤ F (y i) - F (x i) := by
        induction i with
        | zero => change 0 ≤ F x₀ - F x₀; simp
        | succ i ih =>
          rw [frec]
          have he : 0 ≤ F (y i) - F (x (i+1)) := by linarith only [ih, dropnn i]
          nlinarith only [mul_nonneg (sq_nonneg (w i)) he]
      have gappos (i) (hi0 : 0 < i) (hi : i < m) : 0 < F (y i) - F (x i) := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi0)
        rw [frec]
        have he : 0 < F (y j) - F (x (j+1)) := by
          linarith only [gapnn j, droppos j (by omega)]
        nlinarith only [mul_pos (sq_pos_of_pos (wpos j hi)) he]
      have fstrict (i) (hi : i+1 ≤ m) : F (y (i+1)) < F (y i) := by
        have he : 0 < F (y i) - F (x (i+1)) := by
          linarith only [gapnn i, droppos i (by omega)]
        have hw : (w i)^2 < 1 := by nlinarith only [wnn i, wlt i]
        rw [frec]
        nlinarith only [mul_pos (sub_pos.mpr hw) he]
      have fmono (i) : F (y (i+1)) ≤ F (y i) := by
        by_cases hi : i < m
        · exact le_of_lt (fstrict i (by omega))
        · rw [ystop i (by omega), ystop (i+1) (by omega),
            (stopped i (by omega)).2, (stopped (i+1) (by omega)).2]
      have identity (i) : F (y i) = F (x i) + (S i)^2 *
          ∑ j ∈ Finset.range i, (F (x j) - F (x (j+1))) / (S j)^2 := by
        induction i with
        | zero => simp [F, y, x, smoothX, smoothed, cgIter]
        | succ i ih =>
          by_cases hi : i < m
          · rw [Finset.sum_range_succ, frec, ih, wratio i hi]
            field_simp [ne_of_gt (spos i hi)]
            <;> ring
          · rw [ystop (i+1) (by omega), szero (i+1) (by omega)]
            simp
      exact ⟨identity, (fun i hi0 hi => sub_pos.mp (gappos i hi0 hi)),
        fstrict, fmono, rfl, ystop m (le_refl _)⟩
