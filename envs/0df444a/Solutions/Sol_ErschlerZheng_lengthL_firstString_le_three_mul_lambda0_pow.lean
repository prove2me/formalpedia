-- Prove2me | solution 1 for ErschlerZheng.lengthL_firstString_le_three_mul_lambda0_pow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T10:42:41.964454+00:00
-- url     : https://prove2.me/submissions/94c83f38-17bc-49c7-b00a-aeb96be9f230

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Theorems.Thm_ErschlerZheng_existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM

section
/-!
# The cubic `x³ - x² - 2x - 4`: positive roots exceed 2 and lie in `(2.4675, 2.4676)`
-/

namespace ErschlerZheng

namespace CubicBase

theorem pos_root_gt_two {x : ℝ} (hx : 0 < x) (h : x ^ 3 - x ^ 2 - 2 * x - 4 = 0) : 2 < x := by
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hc), mul_nonneg (mul_nonneg hx.le hx.le)
    (sub_nonneg.mpr hc)]

theorem pos_root_gt {x : ℝ} (h0 : 0 < x) (h : x ^ 3 - x ^ 2 - 2 * x - 4 = 0) :
    (24675 : ℝ) / 10000 < x := by
  have h2 := pos_root_gt_two h0 h
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2.le),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2.le)) h0.le]

theorem pos_root_lt {x : ℝ} (h0 : 0 < x) (h : x ^ 3 - x ^ 2 - 2 * x - 4 = 0) :
    x < (24676 : ℝ) / 10000 := by
  have h2 := pos_root_gt_two h0 h
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2.le),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2.le)) h0.le]

end CubicBase

end ErschlerZheng
end

section
/-!
# K1: `L^{(012)}_n ⩽ 3 λ_0^n` (p. 59)

Route.
1. `M_{ω_k} Q^{k+1} = Q^k M` for the cyclic permutation matrix `Q`, so the product
   `M_0 M_1 M_2 M_0 ⋯` (n factors) times `Qⁿ` is `Mⁿ`, and `L_n = 1ᵀ Mⁿ 1` (as `Qⁿ 1 = 1`).
2. Cayley–Hamilton: `x_n = 1ᵀ Mⁿ 1` satisfies `x_{n+3} = x_{n+2} + 2x_{n+1} + 4x_n`.
3. With `λ = λ_0`, `y_n = x_{n+1} - λ x_n` satisfies `y_{n+2} = -(λ-1) y_{n+1} - (4/λ) y_n`, whose
   quadratic form `E_n = y_{n+1}² + (λ-1) y_n y_{n+1} + (4/λ) y_n²` is positive definite with
   `E_{n+1} = (4/λ) E_n`; hence `|y_n| ⩽ K sⁿ` with `K = 3/4`, `s = 1.2733 < λ`.
4. `x_n + D sⁿ ⩽ 3λⁿ` for `n ⩾ 2` by induction, `D = K/(λ - s)`; `n = 0, 1` directly.
-/

namespace ErschlerZheng

namespace LengthBoundDev

open CubicBase Matrix

/-- The cyclic permutation matrix with `M_0 Q = M`. -/
def Qm : Matrix (Fin 3) (Fin 3) ℕ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem Qm_cube : Qm ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qm, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem Qm_pow_mod (n : ℕ) : Qm ^ n = Qm ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, Qm_cube, one_pow, one_mul]

theorem substMatrix_mul_Qm_pow (n : ℕ) :
    substMatrix (firstString n) * Qm ^ (n + 1) = Qm ^ n * matrixM := by
  rw [Qm_pow_mod (n + 1), Qm_pow_mod n]
  have hfs : firstString n = ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩ := rfl
  rw [hfs]
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h | h | h
  · have h' : (n + 1) % 3 = 1 := by omega
    simp only [h, h']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [substMatrix, Qm, matrixM, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  · have h' : (n + 1) % 3 = 2 := by omega
    simp only [h, h']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [substMatrix, Qm, matrixM, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  · have h' : (n + 1) % 3 = 0 := by omega
    simp only [h, h']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [substMatrix, Qm, matrixM, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem prod_mul_Qm_pow (n : ℕ) :
    (List.ofFn fun i : Fin n => substMatrix (firstString i)).prod * Qm ^ n = matrixM ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.prod_concat, mul_assoc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [substMatrix_mul_Qm_pow, ← mul_assoc, ih, pow_succ]

theorem Qm_pow_mulVec_one (n : ℕ) : Qm ^ n *ᵥ (fun _ => 1) = fun _ => 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec]
    have : Qm *ᵥ (fun _ => (1 : ℕ)) = fun _ => 1 := by
      ext i; fin_cases i <;> simp [Qm, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [this, ih]

/-- `v_n = Mⁿ 1`. -/
def vM (n : ℕ) : Fin 3 → ℕ := matrixM ^ n *ᵥ (fun _ => 1)

theorem lengthL_firstString_eq (n : ℕ) : lengthL firstString n = vM n 0 + vM n 1 + vM n 2 := by
  have : lengthL firstString n = (fun _ => 1) ⬝ᵥ (matrixM ^ n *ᵥ fun _ => 1) := by
    unfold lengthL
    rw [← Matrix.dotProduct_mulVec]
    congr 1
    conv_lhs => rw [← Qm_pow_mulVec_one n]
    rw [Matrix.mulVec_mulVec, prod_mul_Qm_pow]
  rw [this]
  simp [dotProduct, Fin.sum_univ_three, vM]

theorem vM_succ (n : ℕ) : vM (n + 1) = matrixM *ᵥ vM n := by
  unfold vM
  rw [pow_succ', ← Matrix.mulVec_mulVec]

theorem vM_rec (n : ℕ) (i : Fin 3) :
    vM (n + 3) i = vM (n + 2) i + 2 * vM (n + 1) i + 4 * vM n i := by
  rw [vM_succ (n + 2), vM_succ (n + 1), vM_succ n]
  generalize vM n = v
  fin_cases i <;>
    simp [matrixM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- `x_n = L_n` as a real sequence. -/
noncomputable def xL (n : ℕ) : ℝ := (lengthL firstString n : ℝ)

theorem xL_rec (n : ℕ) : xL (n + 3) = xL (n + 2) + 2 * xL (n + 1) + 4 * xL n := by
  unfold xL
  rw [lengthL_firstString_eq, lengthL_firstString_eq, lengthL_firstString_eq,
    lengthL_firstString_eq, vM_rec n 0, vM_rec n 1, vM_rec n 2]
  push_cast
  ring

theorem xL_zero : xL 0 = 3 := by
  unfold xL; rw [lengthL_firstString_eq]; simp [vM]

theorem xL_one : xL 1 = 7 := by
  unfold xL; rw [lengthL_firstString_eq]
  simp [vM, matrixM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem xL_two : xL 2 = 17 := by
  unfold xL; rw [lengthL_firstString_eq, vM_succ, vM_succ]
  simp [vM, matrixM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The bound, for any positive root `λ` of the cubic. -/
theorem xL_le (lam : ℝ) (h0 : 0 < lam) (hroot : lam ^ 3 - lam ^ 2 - 2 * lam - 4 = 0) (n : ℕ) :
    xL n ≤ 3 * lam ^ n := by
  have hlo := pos_root_gt h0 hroot
  have hhi := pos_root_lt h0 hroot
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 4 / lam := ⟨_, rfl⟩
  have hqlam : q * lam = 4 := by rw [hq]; field_simp
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = lam - 1 := ⟨_, rfl⟩
  have hpq : lam ^ 2 - lam - q - 2 = 0 := by
    have : lam * (lam ^ 2 - lam - q - 2) = 0 := by linear_combination hroot - hqlam
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  -- the sequence y
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ, y = fun n => xL (n + 1) - lam * xL n := ⟨_, rfl⟩
  have hyrec : ∀ n, y (n + 2) = -p * y (n + 1) - q * y n := by
    intro n
    simp only [hy, hp]
    rw [show n + 2 + 1 = n + 3 by omega, xL_rec n]
    linear_combination (-(xL (n + 1))) * hpq + (-(xL n)) * hqlam
  -- the quadratic form
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℝ, E = fun n => y (n + 1) ^ 2 + p * y n * y (n + 1) + q * y n ^ 2 :=
    ⟨_, rfl⟩
  have hErec : ∀ n, E (n + 1) = q * E n := by
    intro n
    simp only [hE]
    rw [show n + 1 + 1 = n + 2 by omega]
    linear_combination (y (n + 2) - q * y n) * hyrec n
  have hEn : ∀ n, E n = q ^ n * E 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hErec, ih]; ring
  -- numerics
  have hq_lo : (162101 : ℝ) / 100000 < q := by
    rw [hq, lt_div_iff₀ h0]; nlinarith
  have hq_hi : q < (162108 : ℝ) / 100000 := by
    rw [hq, div_lt_iff₀ h0]; nlinarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = q - p ^ 2 / 4 := ⟨_, rfl⟩
  have hc_lo : (108 : ℝ) / 100 < c := by
    simp only [hc, hp]; nlinarith
  have hy0 : y 0 = 7 - 3 * lam := by rw [hy]; simp only [zero_add, xL_zero, xL_one]; ring
  have hy1 : y 1 = 17 - 7 * lam := by
    rw [hy]; simp only [show 1 + 1 = 2 from rfl, xL_one, xL_two]; ring
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 3 / 4 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 12733 / 10000 := ⟨_, rfl⟩
  have hE0 : E 0 ≤ K ^ 2 * c := by
    simp only [hE, hy0, hy1, hc, hp, hK]
    have a1 : (7 - 3 * lam) ^ 2 ≤ (4028 / 10000 : ℝ) ^ 2 := by nlinarith
    have a2 : (17 - 7 * lam) ^ 2 ≤ (2732 / 10000 : ℝ) ^ 2 := by nlinarith
    have a3 : (lam - 1) * (7 - 3 * lam) * (17 - 7 * lam) ≤ (14676 / 10000) * (4028 / 10000) *
        (2732 / 10000 : ℝ) := by
      have b1 : 0 < 3 * lam - 7 := by linarith
      have b2 : 0 < 7 * lam - 17 := by linarith
      have b3 : 3 * lam - 7 ≤ 4028 / 10000 := by linarith
      have b4 : 7 * lam - 17 ≤ 2732 / 10000 := by linarith
      have b5 : lam - 1 ≤ 14676 / 10000 := by linarith
      calc (lam - 1) * (7 - 3 * lam) * (17 - 7 * lam)
          = (lam - 1) * ((3 * lam - 7) * (7 * lam - 17)) := by ring
        _ ≤ (14676 / 10000) * ((4028 / 10000) * (2732 / 10000)) := by
          apply mul_le_mul b5 (mul_le_mul b3 b4 b2.le (by norm_num)) (by positivity)
            (by norm_num)
        _ = _ := by ring
    have a4 : q * (7 - 3 * lam) ^ 2 ≤ (162108 / 100000) * (4028 / 10000 : ℝ) ^ 2 := by
      apply mul_le_mul hq_hi.le a1 (sq_nonneg _) (by norm_num)
    nlinarith
  have hsq : q ≤ s ^ 2 := by simp only [hs]; linarith
  have hyb : ∀ n, y n ≤ K * s ^ n := by
    intro n
    have h1 : c * y n ^ 2 ≤ E n := by
      have : E n - c * y n ^ 2 = (y (n + 1) + p / 2 * y n) ^ 2 := by
        simp only [hE, hc]; ring
      nlinarith [sq_nonneg (y (n + 1) + p / 2 * y n)]
    have h2 : E n ≤ (s ^ 2) ^ n * (K ^ 2 * c) := by
      rw [hEn]
      have hE0nn : 0 ≤ E 0 := by
        have : 0 ≤ c * y 0 ^ 2 := by positivity
        have h10 : c * y 0 ^ 2 ≤ E 0 := by
          have : E 0 - c * y 0 ^ 2 = (y (0 + 1) + p / 2 * y 0) ^ 2 := by
            simp only [hE, hc]; ring
          nlinarith [sq_nonneg (y (0 + 1) + p / 2 * y 0)]
        linarith
      apply mul_le_mul (pow_le_pow_left₀ (by linarith) hsq n) hE0 hE0nn (by positivity)
    have h3 : y n ^ 2 ≤ (K * s ^ n) ^ 2 := by
      have : c * y n ^ 2 ≤ c * (K * s ^ n) ^ 2 := by
        calc c * y n ^ 2 ≤ (s ^ 2) ^ n * (K ^ 2 * c) := h1.trans h2
          _ = c * (K * s ^ n) ^ 2 := by ring
      exact le_of_mul_le_mul_left this (by linarith)
    by_contra hcon
    push Not at hcon
    have hKs : 0 ≤ K * s ^ n := by positivity
    nlinarith [mul_self_lt_mul_self hKs hcon]
  have hls : 0 < lam - s := by rw [hs]; linarith
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = K / (lam - s) := ⟨_, rfl⟩
  have hDK : D * (lam - s) = K := by rw [hD]; field_simp
  have hD0 : 0 ≤ D := by rw [hD, hK]; positivity
  have hDb : D ≤ 63 / 100 := by
    rw [hD, div_le_iff₀ hls, hK, hs]; nlinarith
  have hs0 : 0 ≤ s := by rw [hs]; norm_num
  have hxrec1 : ∀ n, xL (n + 1) = lam * xL n + y n := by intro n; rw [hy]; ring
  have key : ∀ n, 2 ≤ n → xL n + D * s ^ n ≤ 3 * lam ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [xL_two]
      have h1 : D * s ^ 2 ≤ 63 / 100 * (12733 / 10000) ^ 2 := by
        rw [hs]; exact mul_le_mul_of_nonneg_right hDb (by positivity)
      nlinarith
    | succ n hn ih =>
      rw [hxrec1]
      have := hyb n
      calc lam * xL n + y n + D * s ^ (n + 1) ≤ lam * xL n + K * s ^ n + D * s ^ (n + 1) := by
            linarith
        _ = lam * (xL n + D * s ^ n) := by rw [← hDK]; ring
        _ ≤ lam * (3 * lam ^ n) := by gcongr
        _ = 3 * lam ^ (n + 1) := by ring
  rcases n with _ | _ | n
  · rw [xL_zero]; simp
  · rw [xL_one]; simp; linarith
  · have h1 := key (n + 2) (by omega)
    have h2 : 0 ≤ D * s ^ (n + 2) := by positivity
    linarith

end LengthBoundDev

end ErschlerZheng
end

section
open ErschlerZheng
open LengthBoundDev in
theorem solution (n : ℕ) :
    (lengthL firstString n : ℝ) ≤ 3 * lambda0 ^ n := by
  obtain ⟨h0, hroot⟩ := existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM.2.1
  exact xL_le lambda0 h0 hroot n
end
