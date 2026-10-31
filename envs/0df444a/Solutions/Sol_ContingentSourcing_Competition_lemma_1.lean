-- Prove2me | solution 1 for ContingentSourcing.Competition.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:33:22.848878+00:00
-- url     : https://prove2.me/submissions/9505d283-332c-4d79-a0ad-4681a029ce4c

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model
import Theorems.Thm_ContingentSourcing_Competition_proposition_1

open ContingentSourcing.Competition

namespace CSLemma1Aux

lemma PG_pos (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ1 : ρ ≤ 1) : 0 < P.PG ρ := by
  obtain ⟨hm, hp0, hp1, -⟩ := hP
  unfold Params.PG Params.P0
  nlinarith

lemma profit_eq (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ1 : ρ ≤ 1) (w : Prices) (q : Orders) :
    P.buyerProfit ρ w q =
      (1 - P.P1) * ρ * (P.revenue (q.QR + q.QEB) - w.wE * q.QEB - w.wR * q.QR)
      + (1 - P.P1) * (1 - ρ) * (P.revenue (q.QR + q.QEG) - w.wE * q.QEG - w.wR * q.QR)
      + P.P1 * (P.revenue (q.QU + q.QR + q.QEG) - w.wE * q.QEG - w.wR * q.QR - w.wU * q.QU) := by
  have h := (PG_pos P hP ρ hρ1).ne'
  unfold Params.buyerProfit Params.P0G Params.P1G Params.PB
  unfold Params.PG at h ⊢
  unfold Params.P0 at h ⊢
  field_simp
  ring

/-- Lowering prices (componentwise) weakly raises the buyer's profit of any feasible order;
the difference is a sum of price gaps times ordered quantities. -/
lemma profit_diff (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ1 : ρ ≤ 1) (w v : Prices) (q : Orders) :
    P.buyerProfit ρ v q - P.buyerProfit ρ w q =
      (1 - P.P1) * ρ * (w.wE - v.wE) * q.QEB + (w.wR - v.wR) * q.QR
      + ((1 - P.P1) * (1 - ρ) + P.P1) * (w.wE - v.wE) * q.QEG + P.P1 * (w.wU - v.wU) * q.QU := by
  rw [profit_eq P hP ρ hρ1, profit_eq P hP ρ hρ1]; ring

lemma min_eq_or (a m : ℝ) : (min a m = a) ∨ (min a m = m ∧ m < a) := by
  rcases le_or_gt a m with h | h
  · left; exact min_eq_left h
  · right; exact ⟨min_eq_right h.le, h⟩

end CSLemma1Aux

open CSLemma1Aux in
theorem solution (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (w : Prices) (hwU : 0 ≤ w.wU) (hwR : 0 ≤ w.wR) (hRE : w.wR ≤ w.wE) :
    ∃ q : Orders, P.IsOptimalOrder ρ w q ∧ q.QEG = 0 := by
  have hP' := hP
  obtain ⟨hm, hp0, hp1, -⟩ := hP'
  have hq : 0 < 1 - P.P1 := by linarith
  -- clamped prices
  set v : Prices := ⟨min w.wU P.m, min w.wR P.m, min w.wE P.m⟩ with hv
  have vU0 : 0 ≤ v.wU := le_min hwU hm.le
  have vR0 : 0 ≤ v.wR := le_min hwR hm.le
  have vUm : v.wU ≤ P.m := min_le_right _ _
  have vEm : v.wE ≤ P.m := min_le_right _ _
  have vRm : v.wR ≤ P.m := min_le_right _ _
  have vRE : v.wR ≤ v.wE := min_le_min_right _ hRE
  have vUle : v.wU ≤ w.wU := min_le_left _ _
  have vRle : v.wR ≤ w.wR := min_le_left _ _
  have vEle : v.wE ≤ w.wE := min_le_left _ _
  have hprop := proposition_1 P hP ρ hρ0 hρ1 v vU0 vUm vR0 vRE vEm
  have heta1 : P.eta1 ρ v = P.P1 * v.wU + (1 - P.P1) * ρ * v.wE + (1 - P.P1) * (1 - ρ) * P.m := by
    have h := (PG_pos P hP ρ hρ1).ne'
    unfold Params.eta1 Params.P0G Params.PB
    field_simp; unfold Params.P0; ring
  have heta2 : P.eta2 v = P.P1 * v.wU + (1 - P.P1) * v.wE := by unfold Params.eta2 Params.P0; ring
  -- transfer: an order optimal at v whose positive components are bought at unclamped prices
  have transfer : ∀ q : Orders, P.IsOptimalOrder ρ v q →
      (w.wU - v.wU) * q.QU = 0 → (w.wR - v.wR) * q.QR = 0 → (w.wE - v.wE) * q.QEB = 0 →
      q.QEG = 0 → P.IsOptimalOrder ρ w q := by
    intro q ⟨hqf, hqo⟩ zU zR zE zG
    refine ⟨hqf, fun q' hq' => ?_⟩
    have d1 := profit_diff P hP ρ hρ1 w v q'
    have d2 := profit_diff P hP ρ hρ1 w v q
    obtain ⟨g1, g2, g3, g4⟩ := hq'
    have ha : 0 ≤ (1 - P.P1) * ρ := mul_nonneg hq.le hρ0
    have hb : 0 ≤ (1 - P.P1) * (1 - ρ) + P.P1 := by nlinarith
    have t1 := mul_nonneg (mul_nonneg ha (by linarith : 0 ≤ w.wE - v.wE)) g4
    have t2 := mul_nonneg (by linarith : 0 ≤ w.wR - v.wR) g2
    have t3 := mul_nonneg (mul_nonneg hb (by linarith : 0 ≤ w.wE - v.wE)) g3
    have t4 := mul_nonneg (mul_nonneg hp0.le (by linarith : 0 ≤ w.wU - v.wU)) g1
    have := hqo q' ⟨g1, g2, g3, g4⟩
    have e2 : (1 - P.P1) * ρ * (w.wE - v.wE) * q.QEB + (w.wR - v.wR) * q.QR
      + ((1 - P.P1) * (1 - ρ) + P.P1) * (w.wE - v.wE) * q.QEG + P.P1 * (w.wU - v.wU) * q.QU = 0 := by
      rw [zG]
      have : (1 - P.P1) * ρ * (w.wE - v.wE) * q.QEB = (1 - P.P1) * ρ * ((w.wE - v.wE) * q.QEB) := by ring
      have : P.P1 * (w.wU - v.wU) * q.QU = P.P1 * ((w.wU - v.wU) * q.QU) := by ring
      simp only [mul_assoc, zE, zR, zU, mul_zero, add_zero]
    linarith
  have hvU : (w.wU - v.wU) = 0 ∨ v.wU = P.m := by
    rcases min_eq_or w.wU P.m with h | h
    · left; show w.wU - min w.wU P.m = 0; rw [h]; ring
    · right; exact h.1
  have hvR : (w.wR - v.wR) = 0 ∨ v.wR = P.m := by
    rcases min_eq_or w.wR P.m with h | h
    · left; show w.wR - min w.wR P.m = 0; rw [h]; ring
    · right; exact h.1
  have hvE : (w.wE - v.wE) = 0 ∨ v.wE = P.m := by
    rcases min_eq_or w.wE P.m with h | h
    · left; show w.wE - min w.wE P.m = 0; rw [h]; ring
    · right; exact h.1
  obtain ⟨hI, hII, hIII, hIV⟩ := hprop
  by_cases c4 : v.wR ≤ v.wU
  · refine ⟨P.orderIV v, transfer _ (hIV c4) ?_ ?_ ?_ rfl, rfl⟩
    · simp [Params.orderIV]
    · simp only [Params.orderIV]
      rcases hvR with h | h
      · rw [h, zero_mul]
      · rw [h]; ring
    · simp [Params.orderIV]
  push_neg at c4
  have hUeq : w.wU - v.wU = 0 := by
    rcases hvU with h | h
    · exact h
    · exfalso; linarith
  by_cases c1 : P.eta1 ρ v < v.wR
  · refine ⟨P.orderI v, transfer _ (hI c1) ?_ ?_ ?_ rfl, rfl⟩
    · rw [hUeq, zero_mul]
    · simp [Params.orderI]
    · simp only [Params.orderI]
      rcases hvE with h | h
      · rw [h, zero_mul]
      · rw [h]; ring
  push_neg at c1
  by_cases c2 : P.eta2 v < v.wR
  · refine ⟨P.orderII ρ v, transfer _ (hII c2 c1) ?_ ?_ ?_ rfl, rfl⟩
    · rw [hUeq, zero_mul]
    · rcases hvR with h | h
      · rw [h, zero_mul]
      · -- v.wR = m forces η1 = m and Q_R = 0
        have hb : (1 - P.P1) * (1 - ρ) ≠ 0 := by
          intro h0
          have : (1 - ρ) = 0 := by
            rcases mul_eq_zero.mp h0 with h' | h'
            · exfalso; linarith
            · exact h'
          have hρ' : ρ = 1 := by linarith
          have c1' := c1; have c2' := c2
          rw [heta1, hρ'] at c1'; rw [heta2] at c2'
          linarith
        have hn : P.PG ρ * P.P0G ρ * P.m - v.wR + P.PB ρ * v.wE + P.P1 * v.wU = 0 := by
          have e1 : P.PG ρ * P.P0G ρ = (1 - P.P1) * (1 - ρ) := by
            have h := (PG_pos P hP ρ hρ1).ne'
            unfold Params.P0G; field_simp; unfold Params.P0; ring
          have e2 : P.PB ρ = (1 - P.P1) * ρ := by unfold Params.PB Params.P0; ring
          rw [e1, e2]; rw [heta1] at c1
          have : v.wE ≤ P.m := vEm
          have : (1 - P.P1) * ρ * v.wE ≤ (1 - P.P1) * ρ * P.m :=
            mul_le_mul_of_nonneg_left vEm (mul_nonneg hq.le hρ0)
          have : P.P1 * v.wU ≤ P.P1 * P.m := mul_le_mul_of_nonneg_left vUm hp0.le
          nlinarith
        simp only [Params.orderII]; rw [hn]; simp
    · rcases hvE with h | h
      · rw [h, zero_mul]
      · exfalso
        rw [heta1, h] at c1; rw [heta2, h] at c2
        nlinarith
  push_neg at c2
  refine ⟨P.orderIII v, transfer _ (hIII c4 c2) ?_ ?_ ?_ rfl, rfl⟩
  · rw [hUeq, zero_mul]
  · rcases hvR with h | h
    · rw [h, zero_mul]
    · exfalso
      rw [heta2, h] at c2
      have : P.P1 * v.wU < P.P1 * P.m := mul_lt_mul_of_pos_left (by linarith) hp0
      have : (1 - P.P1) * v.wE ≤ (1 - P.P1) * P.m := mul_le_mul_of_nonneg_left vEm hq.le
      nlinarith
  · simp [Params.orderIII]
