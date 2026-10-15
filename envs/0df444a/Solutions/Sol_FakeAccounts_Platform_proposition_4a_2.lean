-- Prove2me | solution 2 for FakeAccounts.Platform.proposition_4a
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-14T19:55:43.255007+00:00
-- url     : https://prove2.me/submissions/112f3c05-28d0-4ed3-a06a-b3342a5f51e2

import Definitions.Def_FakeAccounts_Platform_Setting
namespace FakeAccounts.Platform

lemma fa_meanQ_pos (P : Params) (hP : Standing P) : 0 < meanQ P := by
  unfold meanQ
  have h1 := mul_pos hP.rho_pos (lt_trans hP.qL_pos hP.qL_lt_qH)
  have h2 := mul_pos (sub_pos.mpr hP.rho_lt_one) hP.qL_pos
  linarith

lemma fa_expReal_pool (P : Params) (hP : Standing P) (d : ℝ) :
    expReal P .pool d = 1 - cost P d *
      (P.l * (P.rho / P.qH + (1 - P.rho) / P.qL) + (1 - P.l) / meanQ P) := by
  have hH : P.qH ≠ 0 := (lt_trans hP.qL_pos hP.qL_lt_qH).ne'
  have hL : P.qL ≠ 0 := hP.qL_pos.ne'
  have hE : meanQ P ≠ 0 := (fa_meanQ_pos P hP).ne'
  simp only [expReal, nPay, nUa, nReal, nIn, nUn, postQ, postH, qual]
  unfold meanQ at hE ⊢
  field_simp
  ring

lemma fa_expReal_sep (P : Params) (hP : Standing P) (r : Regime) (hr : r ≠ .pool) (d : ℝ) :
    expReal P r d = 1 - cost P d * (P.rho / P.qH + (1 - P.rho) / P.qL) := by
  have hH : P.qH ≠ 0 := (lt_trans hP.qL_pos hP.qL_lt_qH).ne'
  have hL : P.qL ≠ 0 := hP.qL_pos.ne'
  cases r with
  | pool => exact absurd rfl hr
  | csep =>
    simp [expReal, nPay, nUa, nReal, nIn, nUn, postQ, postH, qual]
    field_simp
    ring
  | nsep =>
    simp [expReal, nPay, nUa, nReal, nIn, nUn, postQ, postH, qual]
    field_simp
    ring

lemma fa_key (P : Params) (hP : Standing P) (d : ℝ) (hd : 0 ≤ d) :
    eqProfit P d ≤ eqProfit P 0 - P.gamma / 2 * d ^ 2 := by
  have hqH : 0 < P.qH := lt_trans hP.qL_pos hP.qL_lt_qH
  have hE := fa_meanQ_pos P hP
  set A := P.rho / P.qH + (1 - P.rho) / P.qL with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ 1 - P.rho := by linarith [hP.rho_lt_one]
    have := hP.rho_pos
    have := hP.qL_pos
    positivity
  have hJ : 1 / meanQ P ≤ A := by
    have : A - 1 / meanQ P =
        P.rho * (1 - P.rho) * (P.qH - P.qL) ^ 2 / (P.qH * P.qL * meanQ P) := by
      have hL : P.qL ≠ 0 := hP.qL_pos.ne'
      have hH : P.qH ≠ 0 := hqH.ne'
      rw [hA]; unfold meanQ at hE ⊢
      have hE' : P.rho * P.qH + (1 - P.rho) * P.qL ≠ 0 := hE.ne'
      field_simp
      ring
    have : 0 ≤ P.rho * (1 - P.rho) * (P.qH - P.qL) ^ 2 / (P.qH * P.qL * meanQ P) := by
      have : 0 ≤ 1 - P.rho := by linarith [hP.rho_lt_one]
      have := hP.rho_pos
      have := hP.qL_pos
      positivity
    linarith
  set Kp := P.l * A + (1 - P.l) / meanQ P with hKp
  have hKpA : Kp ≤ A := by
    have h1 : 0 ≤ 1 - P.l := by linarith [hP.l_lt_one]
    have : (1 - P.l) / meanQ P = (1 - P.l) * (1 / meanQ P) := by ring
    rw [hKp, this]
    nlinarith [mul_le_mul_of_nonneg_left hJ h1]
  have hKp0 : 0 ≤ Kp := by
    have : 0 ≤ 1 - P.l := by linarith [hP.l_lt_one]
    have := hP.l_pos
    positivity
  have hc0 : cost P 0 = P.c0 := by simp [cost]
  have hcd : P.c0 ≤ cost P d := by
    unfold cost
    have : 0 ≤ 1 - P.tau := by linarith [hP.tau_lt_one]
    have := mul_nonneg (mul_nonneg hP.c1_nonneg this) hd
    linarith
  have hcd0 : 0 ≤ cost P d := le_trans hP.c0_nonneg hcd
  have hm : 0 < P.lamP * P.mu := mul_pos hP.lamP_pos hP.mu_pos
  have fin : ∀ K0 K : ℝ, 0 ≤ K0 → K0 ≤ K →
      P.lamP * P.mu * (1 - cost P d * K) - P.gamma / 2 * d ^ 2 ≤
        P.lamP * P.mu * (1 - cost P 0 * K0) - P.gamma / 2 * 0 ^ 2 - P.gamma / 2 * d ^ 2 := by
    intro K0 K h0 hK
    rw [hc0]
    have : P.c0 * K0 ≤ cost P d * K := mul_le_mul hcd hK h0 hcd0
    nlinarith [mul_le_mul_of_nonneg_left this hm.le]
  unfold eqProfit profit eqRegime
  by_cases h : 0 < d1 P
  · rw [if_pos (show 0 < d1 P ∧ (0:ℝ) ≤ d1 P from ⟨h, h.le⟩), fa_expReal_pool P hP 0]
    split_ifs
    · rw [fa_expReal_pool P hP d]; exact fin _ _ hKp0 le_rfl
    · rw [fa_expReal_sep P hP _ (by intro h; cases h) d]; exact fin _ _ hKp0 hKpA
    · rw [fa_expReal_sep P hP _ (by intro h; cases h) d]; exact fin _ _ hKp0 hKpA
  · have hn : ∀ x : ℝ, ¬ (0 < d1 P ∧ x ≤ d1 P) := fun x hx => h hx.1
    rw [if_neg (hn 0), if_neg (hn d)]
    split_ifs <;>
      rw [fa_expReal_sep P hP _ (by intro h; cases h) d, fa_expReal_sep P hP _ (by intro h; cases h) 0] <;>
      exact fin _ _ hA0 le_rfl

theorem proposition_4a (P : Params) (hP : Standing P) :
    IsMaxOn (eqProfit P) (Set.Ici 0) 0 ∧ ∀ d, 0 < d → eqProfit P d < eqProfit P 0 := by
  constructor
  · intro d hd
    have hd' : (0:ℝ) ≤ d := hd
    have := fa_key P hP d hd'
    have : 0 ≤ P.gamma / 2 * d ^ 2 := by have := hP.gamma_pos; positivity
    show eqProfit P d ≤ eqProfit P 0
    linarith
  · intro d hd
    have := fa_key P hP d hd.le
    have : 0 < P.gamma / 2 * d ^ 2 := by have := hP.gamma_pos; positivity
    linarith

end FakeAccounts.Platform


-- Platform entry point: restates the target verbatim.
namespace FakeAccounts.Platform

/-- Proposition 4(a), p. 8877: a purely profit-driven platform (w = 0) optimally chooses zero
antifake effort; zero is the unique maximizer of its equilibrium profit over d ≥ 0. -/
theorem _root_.solution (P : Params) (hP : Standing P) :
    IsMaxOn (eqProfit P) (Set.Ici 0) 0 ∧ ∀ d, 0 < d → eqProfit P d < eqProfit P 0 := by
  apply @FakeAccounts.Platform.proposition_4a <;> assumption

end FakeAccounts.Platform
