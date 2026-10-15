-- Prove2me | solution 1 for FakeAccounts.Platform.lemma_8b2
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-14T23:20:07.287492+00:00
-- url     : https://prove2.me/submissions/e9829347-30be-4a5f-9d29-479a6d06a549

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting
import Theorems.Thm_FakeAccounts_Platform_d1_lt_d2
import Theorems.Thm_FakeAccounts_Platform_uninformed_jensen
set_option autoImplicit false
noncomputable section
open FakeAccounts.Platform Set

private lemma mean_pos (P : Params) (h : Standing P) : 0 < meanQ P := by
  unfold meanQ
  exact add_pos (mul_pos h.rho_pos (h.qL_pos.trans h.qL_lt_qH))
    (mul_pos (sub_pos.mpr h.rho_lt_one) h.qL_pos)

private def sepFollowers (P : Params) (d : ℝ) : ℝ :=
  P.rho * (1 - cost P d / P.qH) + (1 - P.rho) * (1 - cost P d / P.qL)

private lemma followers_formula (P : Params) (r : Regime) (d : ℝ) :
    expReal P r d = match r with
      | .pool => P.l * sepFollowers P d + (1-P.l) * (1-cost P d / meanQ P)
      | .csep => sepFollowers P d
      | .nsep => sepFollowers P d := by
  cases r <;> simp [expReal, nPay, nUa, nReal, nIn, nUn, postQ, postH, qual, meanQ, sepFollowers] <;> ring

private lemma sep_eq (P : Params) (d : ℝ) : profit P .nsep d = profit P .csep d := by
  simp only [profit, followers_formula]

private lemma cost_mono (P : Params) (h : Standing P) : Monotone (cost P) := by
  intro x y hxy
  unfold cost
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy
    (mul_nonneg h.c1_nonneg (sub_nonneg.mpr h.tau_lt_one.le)))

private lemma cost_nonneg (P : Params) (h : Standing P) {d : ℝ} (hd : 0 ≤ d) : 0 ≤ cost P d := by
  unfold cost
  positivity [h.c0_nonneg, h.c1_nonneg, h.tau_lt_one.le]

private lemma decreasing_profit (P : Params) (h : Standing P) :
    ∀ r : Regime, StrictAntiOn (profit P r) (Ici 0) := by
  have hρ := h.rho_pos.le
  have hρ' := sub_nonneg.mpr h.rho_lt_one.le
  have hl := h.l_pos.le
  have hl' := sub_nonneg.mpr h.l_lt_one.le
  have hqH := (h.qL_pos.trans h.qL_lt_qH).le
  have hqL := h.qL_pos.le
  have hE := (mean_pos P h).le
  intro r x hx y hy hxy
  have hc := cost_mono P h hxy.le
  have hs : sepFollowers P y ≤ sepFollowers P x := by
    unfold sepFollowers
    gcongr
  have hf : expReal P r y ≤ expReal P r x := by
    rw [followers_formula, followers_formula]
    cases r
    · dsimp
      gcongr
    · exact hs
    · exact hs
  have hrev := mul_le_mul_of_nonneg_left hf (mul_pos h.lamP_pos h.mu_pos).le
  have hsquare : x^2 < y^2 := by nlinarith [show 0 ≤ x from hx]
  have hpen := mul_lt_mul_of_pos_left hsquare (by linarith [h.gamma_pos] : 0 < P.gamma/2)
  unfold profit
  linarith

private lemma pool_difference (P : Params) (d : ℝ) :
    expReal P .pool d - expReal P .csep d =
      nUn P (meanQ P) d - (P.rho * nUn P P.qH d + (1-P.rho)*nUn P P.qL d) := by
  simp only [followers_formula]
  unfold sepFollowers nUn
  ring

private lemma pool_dominates (P : Params) (h : Standing P) (d : ℝ) (hd : 0 ≤ d) :
    expReal P .csep d ≤ expReal P .pool d ∧
      (0 < cost P d → expReal P .csep d < expReal P .pool d) := by
  have hs : 0 < cost P d → expReal P .csep d < expReal P .pool d := by
    intro hc
    have hh := uninformed_jensen P h d hc
    have he := pool_difference P d
    linarith
  refine ⟨?_, hs⟩
  by_cases hc : 0 < cost P d
  · exact (hs hc).le
  · have hz : cost P d = 0 := le_antisymm (le_of_not_gt hc) (cost_nonneg P h hd)
    simp [followers_formula, sepFollowers, hz]

private lemma profit_pool_ge (P : Params) (h : Standing P) (d : ℝ) (hd : 0 ≤ d) :
    profit P .csep d ≤ profit P .pool d := by
  unfold profit
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left (pool_dominates P h d hd).1
    (mul_pos h.lamP_pos h.mu_pos).le) _

private lemma equilibrium_strict (P : Params) (h : Standing P) :
    ∀ d, 0 < d → eqProfit P d < eqProfit P 0 := by
  intro d hd
  have hmon := decreasing_profit P h
  by_cases hpos : 0 < d1 P
  · have h0 : eqProfit P 0 = profit P .pool 0 := by
      simp [eqProfit, eqRegime, hpos, hpos.le]
    rw [h0]
    unfold eqProfit
    cases he : eqRegime P d with
    | pool => exact hmon .pool (by simp) hd.le hd
    | csep => exact (hmon .csep (by simp) hd.le hd).trans_le (profit_pool_ge P h 0 le_rfl)
    | nsep =>
      rw [sep_eq]
      exact (hmon .csep (by simp) hd.le hd).trans_le (profit_pool_ge P h 0 le_rfl)
  · have he (x : ℝ) : eqProfit P x = profit P .csep x := by
      unfold eqProfit eqRegime
      simp only [hpos, false_and, ite_false]
      split_ifs <;> simp only [sep_eq]
    rw [he, he]
    exact hmon .csep (by simp) hd.le hd
theorem solution (P : Params) (hP : Standing P) :
    0 < d1 P → profit P .nsep (d2 P) < profit P .csep (d1 P) := by

  intro hd1
  have ht := d1_lt_d2 P hP
  rw [sep_eq]
  exact decreasing_profit P hP .csep hd1.le ((hd1.trans ht).le) ht

#print axioms solution
