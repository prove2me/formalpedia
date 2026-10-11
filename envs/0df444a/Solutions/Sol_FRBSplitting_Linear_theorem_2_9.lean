-- Prove2me | solution 1 for FRBSplitting.Linear.theorem_2_9
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T22:29:30.283816+00:00
-- url     : https://prove2.me/submissions/f040cd6e-30f9-4f24-86e4-cd003bad3252

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linear_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace RRAux_FRBSplitting_Linear_theorem_2_9

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem fr_key (B : H → H) (u v w xs : H) (lam m L : ℝ) (hlam : 0 < lam) (hL : 0 ≤ L)
    (hsm : m * ‖u - xs‖ ^ 2 ≤
      ⟪u - xs, lam⁻¹ • ((v - lam • B v - lam • (B v - B w)) - u) - -B xs⟫_ℝ)
    (hmono : 0 ≤ ⟪u - xs, B u - B xs⟫_ℝ)
    (hlip : ‖B v - B w‖ ≤ L * ‖v - w‖) :
    (1 + 2 * lam * m) * ‖u - xs‖ ^ 2 - 2 * lam * ⟪u - xs, B u - B v⟫_ℝ
      + (1 - lam * L) * ‖u - v‖ ^ 2
      ≤ ‖v - xs‖ ^ 2 - 2 * lam * ⟪v - xs, B v - B w⟫_ℝ + lam * L * ‖v - w‖ ^ 2 := by
  have E1 : lam⁻¹ • ((v - lam • B v - lam • (B v - B w)) - u) - -B xs
      = lam⁻¹ • (v - u) - ((B u - B xs) - (B u - B v)) - (B v - B w) := by
    rw [smul_sub, smul_sub, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul,
      one_smul, smul_sub]
    abel
  rw [E1, inner_sub_right, inner_sub_right, inner_sub_right, inner_smul_right] at hsm
  have h1 := mul_le_mul_of_nonneg_left hsm hlam.le
  have e1 : lam * (lam⁻¹ * ⟪u - xs, v - u⟫_ℝ) = ⟪u - xs, v - u⟫_ℝ := by
    rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]
  have e2 : v - xs = (u - xs) - (u - v) := by abel
  have e3 : v - u = -(u - v) := by abel
  have e4 : u - xs = (v - xs) + (u - v) := by abel
  have n1 : ‖v - xs‖ ^ 2 = ‖u - xs‖ ^ 2 - 2 * ⟪u - xs, u - v⟫_ℝ + ‖u - v‖ ^ 2 := by
    rw [e2, norm_sub_sq_real]
  have i1 : ⟪u - xs, v - u⟫_ℝ = -⟪u - xs, u - v⟫_ℝ := by rw [e3, inner_neg_right]
  have i2 : ⟪u - xs, B v - B w⟫_ℝ = ⟪v - xs, B v - B w⟫_ℝ + ⟪u - v, B v - B w⟫_ℝ := by
    conv_lhs => rw [e4]
    rw [inner_add_left]
  have c1 : -(‖u - v‖ * (L * ‖v - w‖)) ≤ ⟪u - v, B v - B w⟫_ℝ := by
    have h := abs_real_inner_le_norm (u - v) (B v - B w)
    have h' := mul_le_mul_of_nonneg_left hlip (norm_nonneg (u - v))
    have := neg_abs_le ⟪u - v, B v - B w⟫_ℝ
    linarith
  have c2 : 2 * (‖u - v‖ * ‖v - w‖) ≤ ‖u - v‖ ^ 2 + ‖v - w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖u - v‖ - ‖v - w‖)]
  have c3 : lam * L * (2 * (‖u - v‖ * ‖v - w‖)) ≤ lam * L * (‖u - v‖ ^ 2 + ‖v - w‖ ^ 2) :=
    mul_le_mul_of_nonneg_left c2 (mul_nonneg hlam.le hL)
  have hm2 : 0 ≤ lam * ⟪u - xs, B u - B xs⟫_ℝ := mul_nonneg hlam.le hmono
  simp only [mul_sub] at h1
  rw [e1, i1, i2] at h1
  rw [n1]
  nlinarith

theorem contract (lam m L ε e D I : ℝ) (hlam : 0 < lam) (hL : 0 < L) (hε : 0 ≤ ε)
    (he : 0 ≤ e) (hD : 0 ≤ D) (hI : |I| ≤ e * (L * D))
    (h1 : ε * (1 + lam * L) ≤ 2 * lam * m) (h2 : 2 * ε * lam * L ≤ 1 - 2 * lam * L) :
    (1 + ε) * (e ^ 2 - 2 * lam * I + lam * L * D ^ 2)
      ≤ (1 + 2 * lam * m) * e ^ 2 - 2 * lam * I + (1 - lam * L) * D ^ 2 := by
  have hI' : -I ≤ e * (L * D) := (neg_le_abs I).trans hI
  have hlL : 0 ≤ lam * L := by positivity
  have c2 : 2 * (e * D) ≤ e ^ 2 + D ^ 2 := by nlinarith [sq_nonneg (e - D)]
  have c3 : ε * lam * (-I) ≤ ε * lam * (e * (L * D)) :=
    mul_le_mul_of_nonneg_left hI' (by positivity)
  have c4 : ε * lam * L * (2 * (e * D)) ≤ ε * lam * L * (e ^ 2 + D ^ 2) :=
    mul_le_mul_of_nonneg_left c2 (by positivity)
  have c5 : e ^ 2 * (ε * (1 + lam * L)) ≤ e ^ 2 * (2 * lam * m) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg e)
  have c6 : D ^ 2 * (2 * ε * lam * L) ≤ D ^ 2 * (1 - 2 * lam * L) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg D)
  nlinarith

theorem lower (lam L e D I : ℝ) (hlam : 0 < lam) (hL : 0 < L) (hlL : lam * L ≤ 1 / 2)
    (he : 0 ≤ e) (hD : 0 ≤ D) (hI : |I| ≤ e * (L * D)) :
    e ^ 2 / 2 ≤ e ^ 2 - 2 * lam * I + lam * L * D ^ 2 := by
  have hI' : I ≤ e * (L * D) := (le_abs_self I).trans hI
  have c2 : 2 * (e * D) ≤ e ^ 2 + D ^ 2 := by nlinarith [sq_nonneg (e - D)]
  have c3 : lam * I ≤ lam * (e * (L * D)) := mul_le_mul_of_nonneg_left hI' hlam.le
  have c4 : lam * L * (2 * (e * D)) ≤ lam * L * (e ^ 2 + D ^ 2) :=
    mul_le_mul_of_nonneg_left c2 (by positivity)
  have c5 : lam * L * e ^ 2 ≤ 1 / 2 * e ^ 2 := mul_le_mul_of_nonneg_right hlL (sq_nonneg e)
  nlinarith

end RRAux_FRBSplitting_Linear_theorem_2_9

open RRAux_FRBSplitting_Linear_theorem_2_9

open FRBSplitting.Linear in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (m L lam : ℝ)
    (hA : IsMaximalMonotone A)
    (hm : 0 < m) (hAs : IsStronglyMonotoneOp m A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hzer : (FRBSplitting.Weak.zeroSet A B).Nonempty)
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / (2 * L))
    (x : ℕ → H) (hrun : FRBSplitting.Weak.IsFRBRun J B (fun _ => lam) x) :
    ∃ xs : H, FRBSplitting.Weak.zeroSet A B = {xs} ∧
      ∃ q M : ℝ, 0 < q ∧ q < 1 ∧ ∀ k : ℕ, ‖x k - xs‖ ≤ M * q ^ k := by
  obtain ⟨xs, hxs⟩ := hzer
  have hxs' : -B xs ∈ A xs := hxs
  refine ⟨xs, ?_, ?_⟩
  · ext y
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hy
      have hy' : -B y ∈ A y := hy
      have h1 := hAs y xs _ _ hy' hxs'
      have h2 := hBm y xs
      have e : -B y - -B xs = -(B y - B xs) := by abel
      rw [e, inner_neg_right] at h1
      have h3 : m * ‖y - xs‖ ^ 2 ≤ 0 := by linarith
      have h4 : ‖y - xs‖ ^ 2 ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith
      have h5 : ‖y - xs‖ = 0 := by nlinarith [norm_nonneg (y - xs)]
      exact sub_eq_zero.1 (norm_eq_zero.1 h5)
    · intro hy; rw [hy]; exact hxs
  · have hlL : lam * L < 1 / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hlam1; linarith
    set Φ : ℕ → ℝ := fun j => ‖x (j + 1) - xs‖ ^ 2
        - 2 * lam * ⟪x (j + 1) - xs, B (x (j + 1)) - B (x j)⟫_ℝ
        + lam * L * ‖x (j + 1) - x j‖ ^ 2 with hΦ
    set ε := min (2 * lam * m / (1 + lam * L)) ((1 - 2 * lam * L) / (2 * lam * L)) with hεdef
    have hε : 0 < ε := lt_min (by positivity) (div_pos (by linarith) (by positivity))
    have hε1 : ε * (1 + lam * L) ≤ 2 * lam * m := by
      have := min_le_left (2 * lam * m / (1 + lam * L)) ((1 - 2 * lam * L) / (2 * lam * L))
      rw [← hεdef, le_div_iff₀ (by positivity)] at this; exact this
    have hε2 : 2 * ε * lam * L ≤ 1 - 2 * lam * L := by
      have := min_le_right (2 * lam * m / (1 + lam * L)) ((1 - 2 * lam * L) / (2 * lam * L))
      rw [← hεdef, le_div_iff₀ (by positivity)] at this; linarith
    have hIb : ∀ j, |⟪x (j + 1) - xs, B (x (j + 1)) - B (x j)⟫_ℝ|
        ≤ ‖x (j + 1) - xs‖ * (L * ‖x (j + 1) - x j‖) := by
      intro j
      have h := abs_real_inner_le_norm (x (j + 1) - xs) (B (x (j + 1)) - B (x j))
      have h' := mul_le_mul_of_nonneg_left (hBL (x (j + 1)) (x j)) (norm_nonneg (x (j + 1) - xs))
      linarith
    have hlow : ∀ j, ‖x (j + 1) - xs‖ ^ 2 / 2 ≤ Φ j := fun j =>
      lower lam L _ _ _ hlam0 hL hlL.le (norm_nonneg _) (norm_nonneg _) (hIb j)
    have hstep : ∀ j, (1 + ε) * Φ (j + 1) ≤ Φ j := by
      intro j
      have hr := hrun j
      simp only at hr
      have ha := hJ lam hlam0
        (x (j + 1) - lam • B (x (j + 1)) - lam • (B (x (j + 1)) - B (x j)))
      rw [← hr] at ha
      have hsm := hAs _ _ _ _ ha hxs'
      have hk := fr_key B (x (j + 2)) (x (j + 1)) (x j) xs lam m L hlam0 hL.le hsm
        (hBm (x (j + 2)) xs) (hBL (x (j + 1)) (x j))
      have hc := contract lam m L ε ‖x (j + 1 + 1) - xs‖ ‖x (j + 1 + 1) - x (j + 1)‖
        ⟪x (j + 1 + 1) - xs, B (x (j + 1 + 1)) - B (x (j + 1))⟫_ℝ hlam0 hL hε.le
        (norm_nonneg _) (norm_nonneg _) (hIb (j + 1)) hε1 hε2
      simp only [hΦ]
      exact hc.trans hk
    set ρ := 1 / (1 + ε) with hρ
    have hρ0 : 0 < ρ := by positivity
    have hρ1 : ρ < 1 := by rw [hρ, div_lt_one (by linarith)]; linarith
    have hdec : ∀ j, Φ j ≤ ρ ^ j * Φ 0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h1 : Φ (j + 1) ≤ ρ * Φ j := by
          rw [hρ, one_div_mul_eq_div, le_div_iff₀ (by linarith)]
          linarith [hstep j]
        calc Φ (j + 1) ≤ ρ * Φ j := h1
          _ ≤ ρ * (ρ ^ j * Φ 0) := mul_le_mul_of_nonneg_left ih hρ0.le
          _ = ρ ^ (j + 1) * Φ 0 := by ring
    have hΦ0 : 0 ≤ Φ 0 := le_trans (by positivity) (hlow 0)
    set q := Real.sqrt ρ with hq
    have hq0 : 0 < q := Real.sqrt_pos.2 hρ0
    have hq1 : q < 1 := by rw [hq, Real.sqrt_lt' one_pos]; simpa using hρ1
    have hqρ : q ^ 2 = ρ := Real.sq_sqrt hρ0.le
    refine ⟨q, Real.sqrt (2 * Φ 0) / q + ‖x 0 - xs‖, hq0, hq1, ?_⟩
    intro k
    cases k with
    | zero =>
      simp only [pow_zero, mul_one]
      have : 0 ≤ Real.sqrt (2 * Φ 0) / q := by positivity
      linarith
    | succ j =>
      have h1 : ‖x (j + 1) - xs‖ ^ 2 ≤ (Real.sqrt (2 * Φ 0) * q ^ j) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm j 2, pow_mul, hqρ]
        have := hlow j
        have := hdec j
        nlinarith
      have h2 : ‖x (j + 1) - xs‖ ≤ Real.sqrt (2 * Φ 0) * q ^ j :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
      have h3 : Real.sqrt (2 * Φ 0) * q ^ j
          ≤ (Real.sqrt (2 * Φ 0) / q + ‖x 0 - xs‖) * q ^ (j + 1) := by
        rw [add_mul, pow_succ]
        have e : Real.sqrt (2 * Φ 0) / q * (q ^ j * q) = Real.sqrt (2 * Φ 0) * q ^ j := by
          field_simp
        rw [e]
        have : 0 ≤ ‖x 0 - xs‖ * (q ^ j * q) := by positivity
        linarith
      exact h2.trans h3

#print axioms solution
