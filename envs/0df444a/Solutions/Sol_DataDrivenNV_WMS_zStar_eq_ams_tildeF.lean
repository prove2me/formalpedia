-- Prove2me | solution 1 for DataDrivenNV.WMS.zStar_eq_ams_tildeF
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:56:28.832045+00:00
-- url     : https://prove2.me/submissions/7c142143-8914-4b28-b0d7-708525dddea2

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

open MeasureTheory Set DataDrivenNV.WMS

private lemma left_indicator (f : ℝ → ℝ) {L U q : ℝ} (hL : L ≤ q) (hU : q ≤ U) :
    (∫ x in Iic q, (Icc L U).indicator f x) = ∫ x in L..q, f x := by
  rw [setIntegral_indicator measurableSet_Icc]
  have he : Iic q ∩ Icc L U = Icc L q := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor <;> intro hx
    · exact ⟨hx.2.1, hx.1⟩
    · exact ⟨hx.2, hx.1, hx.2.trans hU⟩
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL]

private lemma right_indicator (f : ℝ → ℝ) {L U q : ℝ} (hL : L ≤ q) (hU : q ≤ U) :
    (∫ x in Ici q, (Icc L U).indicator f x) = ∫ x in q..U, f x := by
  rw [setIntegral_indicator measurableSet_Icc]
  have he : Ici q ∩ Icc L U = Icc q U := by
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor <;> intro hx
    · exact ⟨hx.1, hx.2.2⟩
    · exact ⟨hx.1, hL.trans hx.1, hx.2⟩
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hU]

private lemma exp_integral (q g k L U : ℝ) (hk : k ≠ 0) :
    (∫ x in L..U, g * Real.exp (k*(x-q))) =
      g/k * Real.exp (k*(U-q)) - g/k * Real.exp (k*(L-q)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => g/k * Real.exp (k*(x-q)))
  · intro x hx
    convert (((hasDerivAt_id x).sub_const q).const_mul k).exp.const_mul (g/k) using 1 <;>
      (try rfl) <;> simp only [id_eq, mul_one] <;> field_simp [hk] <;> ring
  · exact (by fun_prop : Continuous (fun x => g*Real.exp (k*(x-q)))).intervalIntegrable _ _

private lemma moment_integral (q g k L U : ℝ) (hk : k ≠ 0) :
    (∫ x in L..U, x * (g * Real.exp (k*(x-q)))) =
      g/k * (U-1/k) * Real.exp (k*(U-q)) -
      g/k * (L-1/k) * Real.exp (k*(L-q)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => g/k * (x-1/k) * Real.exp (k*(x-q)))
  · intro x hx
    convert ((((hasDerivAt_id x).sub_const (1/k)).const_mul (g/k)).mul
      (((hasDerivAt_id x).sub_const q).const_mul k).exp) using 1 <;>
      (try rfl) <;> simp only [id_eq, mul_one] <;> field_simp [hk] <;> ring
  · exact (by fun_prop : Continuous (fun x => x*(g*Real.exp (k*(x-q))))).intervalIntegrable _ _

theorem solution (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (q γ₀ γ₁ : ℝ) (hγ₀ : 0 < γ₀) (hγ₁ : γ₁ ≠ 0)
    (hlo : -((b + h) / h) < γ₁ / γ₀) (hhi : γ₁ / γ₀ < (b + h) / b) :
    ams (tildeF b h q γ₀ γ₁) q = zStar b h γ₀ γ₁ := by
  let A := 1-γ₁/γ₀*(b/(b+h))
  let B := 1+γ₁/γ₀*(h/(b+h))
  have hsum : 0 < b+h := add_pos hb hh
  have hhi' : γ₁*b < (b+h)*γ₀ := by
    have ht := (div_lt_iff₀ hγ₀).mp hhi
    have := (mul_lt_mul_of_pos_right ht hb)
    field_simp at this
    nlinarith
  have hlo' : -(b+h)*γ₀ < γ₁*h := by
    have ht := (lt_div_iff₀ hγ₀).mp hlo
    have := mul_lt_mul_of_pos_right ht hh
    field_simp at this
    nlinarith
  have hA : 0 < A := by
    have he : A = ((b+h)*γ₀-γ₁*b)/(γ₀*(b+h)) := by dsimp [A]; field_simp <;> ring
    rw [he]; exact div_pos (by linarith) (mul_pos hγ₀ hsum)
  have hB : 0 < B := by
    have he : B = ((b+h)*γ₀+γ₁*h)/(γ₀*(b+h)) := by dsimp [B]; field_simp <;> ring
    rw [he]; exact div_pos (by linarith) (mul_pos hγ₀ hsum)
  have hL : tildeLo b h q γ₀ γ₁ ≤ q := by
    unfold tildeLo
    change q+1/γ₁*Real.log A ≤ q
    rcases lt_or_gt_of_ne hγ₁ with hk | hk
    · have h1 : 1 < A := by
        dsimp [A]
        have := mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos hk hγ₀) (div_pos hb hsum)
        linarith
      have := mul_nonpos_of_nonpos_of_nonneg (one_div_neg.mpr hk).le (Real.log_pos h1).le
      linarith
    · have h1 : A < 1 := by
        dsimp [A]
        have := mul_pos (div_pos hk hγ₀) (div_pos hb hsum)
        linarith
      have := mul_nonpos_of_nonneg_of_nonpos (one_div_pos.mpr hk).le (Real.log_neg hA h1).le
      linarith
  have hU : q ≤ tildeHi b h q γ₀ γ₁ := by
    unfold tildeHi
    change q ≤ q+1/γ₁*Real.log B
    rcases lt_or_gt_of_ne hγ₁ with hk | hk
    · have h1 : B < 1 := by
        dsimp [B]
        have := mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos hk hγ₀) (div_pos hh hsum)
        linarith
      have := mul_nonneg_of_nonpos_of_nonpos (one_div_neg.mpr hk).le (Real.log_neg hB h1).le
      linarith
    · have h1 : 1 < B := by
        dsimp [B]
        have := mul_pos (div_pos hk hγ₀) (div_pos hh hsum)
        linarith
      have := mul_nonneg (one_div_pos.mpr hk).le (Real.log_pos h1).le
      linarith
  have eL : Real.exp (γ₁*(tildeLo b h q γ₀ γ₁-q)) = A := by
    rw [show γ₁*(tildeLo b h q γ₀ γ₁-q) = Real.log A by unfold tildeLo; dsimp [A]; field_simp <;> ring]
    exact Real.exp_log hA
  have eU : Real.exp (γ₁*(tildeHi b h q γ₀ γ₁-q)) = B := by
    rw [show γ₁*(tildeHi b h q γ₀ γ₁-q) = Real.log B by unfold tildeHi; dsimp [B]; field_simp <;> ring]
    exact Real.exp_log hB
  have hcdf : cdfOf (tildeF b h q γ₀ γ₁) q = b/(b+h) := by
    unfold cdfOf tildeF
    rw [left_indicator _ hL hU, exp_integral _ _ _ _ _ hγ₁, eL]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    dsimp [A]
    field_simp
    ring
  have hmul : (fun x => x*tildeF b h q γ₀ γ₁ x) =
      (Icc (tildeLo b h q γ₀ γ₁) (tildeHi b h q γ₀ γ₁)).indicator
        (fun x => x*(γ₀*Real.exp (γ₁*(x-q)))) := by
    funext x
    unfold tildeF
    by_cases hx : x ∈ Icc (tildeLo b h q γ₀ γ₁) (tildeHi b h q γ₀ γ₁) <;> simp [hx]
  unfold ams
  rw [hcdf, hmul, left_indicator _ hL hU, right_indicator _ hL hU,
    moment_integral _ _ _ _ _ hγ₁, moment_integral _ _ _ _ _ hγ₁, eL, eU]
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
  unfold zStar tildeLo tildeHi
  dsimp [A, B]
  generalize Real.log (1 - γ₁ / γ₀ * (b / (b + h))) = logA
  generalize Real.log (1 + γ₁ / γ₀ * (h / (b + h))) = logB
  field_simp [hγ₁, hγ₀.ne', hb.ne', hh.ne', hsum.ne']
  ring

#print axioms solution
