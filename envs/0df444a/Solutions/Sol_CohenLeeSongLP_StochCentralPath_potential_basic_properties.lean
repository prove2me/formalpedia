-- Prove2me | solution 1 for CohenLeeSongLP.StochCentralPath.potential_basic_properties
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T23:37:24.337054+00:00
-- url     : https://prove2.me/submissions/547c3c4e-5a7e-49d6-ac11-358a0c7bb8ae

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_Basic

set_option autoImplicit false

namespace CohenLeeSongLP.StochCentralPath.L412

open CohenLeeSongLP.StochCentralPath

theorem L412_cosh_add_le (y u : ℝ) (hu : |u| ≤ 1) :
    Real.cosh (y + u) ≤ Real.cosh y + Real.sinh y * u + Real.cosh y * u ^ 2 := by
  have h1 : Real.exp u ≤ 1 + u + u ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le hu
    have := (abs_le.mp this).2
    linarith
  have h2 : Real.exp (-u) ≤ 1 - u + u ^ 2 := by
    have hu' : |-u| ≤ 1 := by rwa [abs_neg]
    have := Real.abs_exp_sub_one_sub_id_le hu'
    have := (abs_le.mp this).2
    nlinarith
  have hy1 : 0 < Real.exp y := Real.exp_pos y
  have hy2 : 0 < Real.exp (-y) := Real.exp_pos (-y)
  rw [Real.cosh_eq, Real.cosh_eq, Real.sinh_eq, show -(y + u) = -y + -u by ring,
    Real.exp_add, Real.exp_add]
  nlinarith [mul_le_mul_of_nonneg_left h1 hy1.le, mul_le_mul_of_nonneg_left h2 hy2.le]

theorem L412_cosh_sub_one_le (y : ℝ) : Real.cosh y - 1 ≤ |Real.sinh y| := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr h), Real.cosh_eq, Real.sinh_eq]
    have : Real.exp (-y) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [abs_of_nonpos (Real.sinh_nonpos_iff.mpr h), Real.cosh_eq, Real.sinh_eq]
    have : Real.exp y ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    linarith

end CohenLeeSongLP.StochCentralPath.L412

open CohenLeeSongLP.StochCentralPath in
theorem solution {n : ℕ} (hn : 10 ≤ n) (lam : ℝ) (hlam : 0 < lam)
    (r : Fin n → ℝ) :
    (∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1 / lam) →
      potential lam (fun i => r i + v i) ≤
        potential lam r + ∑ i, potentialGrad lam r i * v i + 2 * hessNormSq lam r v) ∧
    lam / Real.sqrt n * (potential lam r - n) ≤ norm2 (potentialGrad lam r) ∧
    Real.sqrt (∑ i, lam ^ 2 * Real.cosh (lam * r i) ^ 2) ≤
      lam * Real.sqrt n + norm2 (potentialGrad lam r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    unfold potential potentialGrad hessNormSq
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hu : |lam * v i| ≤ 1 := by
      rw [abs_mul, abs_of_pos hlam]
      calc lam * |v i| ≤ lam * (1 / lam) := by gcongr; exact hv i
        _ = 1 := by field_simp
    have h := CohenLeeSongLP.StochCentralPath.L412.L412_cosh_add_le (lam * r i) (lam * v i) hu
    have hc : 0 ≤ Real.cosh (lam * r i) * (lam * v i) ^ 2 :=
      mul_nonneg (Real.cosh_pos _).le (sq_nonneg _)
    have e : lam * (r i + v i) = lam * r i + lam * v i := by ring
    rw [e]
    nlinarith [h, hc]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hsum : potential lam r - n ≤ ∑ i, |Real.sinh (lam * r i)| := by
      unfold potential
      have : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      rw [this, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun i _ => CohenLeeSongLP.StochCentralPath.L412.L412_cosh_sub_one_le _
    have hcs : (∑ i, |Real.sinh (lam * r i)|) ≤
        Real.sqrt n * Real.sqrt (∑ i, Real.sinh (lam * r i) ^ 2) := by
      rw [← Real.sqrt_mul hnpos.le]
      apply Real.le_sqrt_of_sq_le
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => |Real.sinh (lam * r i)|)
      simpa [sq_abs] using this
    have hnorm : norm2 (potentialGrad lam r) = lam * Real.sqrt (∑ i, Real.sinh (lam * r i) ^ 2) := by
      unfold norm2 potentialGrad
      have : ∑ i, (lam * Real.sinh (lam * r i)) ^ 2 = lam ^ 2 * ∑ i, Real.sinh (lam * r i) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlam.le]
    rw [hnorm, div_mul_eq_mul_div, div_le_iff₀ hs]
    calc lam * (potential lam r - n) ≤ lam * (Real.sqrt n * Real.sqrt (∑ i, Real.sinh (lam * r i) ^ 2)) := by
          gcongr; exact hsum.trans hcs
      _ = _ := by ring
  · have hnorm : norm2 (potentialGrad lam r) = Real.sqrt (∑ i, (lam * Real.sinh (lam * r i)) ^ 2) := rfl
    have e : ∑ i, lam ^ 2 * Real.cosh (lam * r i) ^ 2 =
        (n : ℝ) * lam ^ 2 + ∑ i, (lam * Real.sinh (lam * r i)) ^ 2 := by
      rw [show (n : ℝ) * lam ^ 2 = ∑ _i : Fin n, lam ^ 2 by simp, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := Real.cosh_sq (lam * r i)
      nlinarith [this]
    rw [e, hnorm]
    have h1 : Real.sqrt ((n : ℝ) * lam ^ 2) = lam * Real.sqrt n := by
      rw [mul_comm, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlam.le]
    rw [← h1]
    have ha : 0 ≤ (n : ℝ) * lam ^ 2 := by positivity
    have hb : 0 ≤ ∑ i, (lam * Real.sinh (lam * r i)) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg ((n : ℝ) * lam ^ 2)) (Real.sqrt_nonneg (∑ i, (lam * Real.sinh (lam * r i)) ^ 2))]

