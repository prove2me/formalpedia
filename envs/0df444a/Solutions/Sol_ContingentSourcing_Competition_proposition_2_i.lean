-- Prove2me | solution 1 for ContingentSourcing.Competition.proposition_2_i
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:38:55.562764+00:00
-- url     : https://prove2.me/submissions/43e5c772-401a-46a2-bd9d-3c77b0c52b62

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

open ContingentSourcing.Competition

namespace CSProp2Dis

noncomputable def P : Params := ⟨10, 1 / 2, 0, 5⟩

lemma Pm : P.m = 10 := rfl
lemma PP1 : P.P1 = 1 / 2 := rfl
lemma PcU : P.cU = 0 := rfl
lemma PcR : P.cR = 5 := rfl

lemma hPB : P.PB 1 = 1 / 2 := by norm_num [Params.PB, Params.P0, P]
lemma hPG : P.PG 1 = 1 / 2 := by norm_num [Params.PG, Params.P0, P]
lemma hP0G : P.P0G 1 = 0 := by norm_num [Params.P0G]
lemma hP1G : P.P1G 1 = 1 := by rw [Params.P1G, hPG, PP1]; norm_num
lemma heta1 (w : Prices) : P.eta1 1 w = w.wU / 2 + w.wE / 2 := by
  simp only [Params.eta1, hPB, hP0G]; norm_num [P]; ring
lemma heta2 (w : Prices) : P.eta2 w = w.wU / 2 + w.wE / 2 := by
  simp only [Params.eta2, Params.P0]; norm_num [P]; ring

/-- Payoffs at ρ = 1 by region. -/
lemma pay_cases (w : Prices) :
    (w.wR ≤ w.wU ∧ P.payU 1 w = 0 ∧ P.payR 1 w = (w.wR - 5) * ((10 - w.wR) / 2)) ∨
    (¬ w.wR ≤ w.wU ∧ w.wU / 2 + w.wE / 2 ≤ w.wR ∧
      P.payU 1 w = (w.wU / 2) * ((10 - w.wU) / 2) ∧
      P.payR 1 w = (1 / 2) * (w.wE - 5) * ((10 - w.wE) / 2)) ∨
    (w.wU < w.wR ∧ w.wR < w.wU / 2 + w.wE / 2 ∧
      P.payU 1 w = (w.wU / 2) * (w.wR - w.wU) ∧
      P.payR 1 w = (w.wR - 5) * (5 - w.wR + w.wU / 2)) := by
  unfold Params.payU Params.payR Params.order
  rw [heta1, heta2]
  split_ifs with h1 h2 h3
  · left
    refine ⟨h1, ?_, ?_⟩ <;> simp only [Params.orderIV, hPB, Pm, PP1, PcU, PcR] <;> ring
  · right; left
    refine ⟨h1, h2, ?_, ?_⟩ <;> simp only [Params.orderI, hPB, Pm, PP1, PcU, PcR] <;> ring
  · exfalso; linarith
  · right; right
    push_neg at h1 h2
    refine ⟨h1, h2, ?_, ?_⟩ <;> simp only [Params.orderIII, Params.P0, hPB, Pm, PP1, PcU, PcR] <;> ring

lemma bounds (w : Prices) (hu0 : 0 ≤ w.wU) (hum : w.wU ≤ 10) (hr : 5 ≤ w.wR) (hre : w.wR ≤ w.wE)
    (he : w.wE ≤ 10) :
    P.payU 1 w ≤ 25 / 4 ∧ (25 / 4 ≤ P.payU 1 w → P.payR 1 w ≤ 25 / 16) := by
  rcases pay_cases w with ⟨h1, hU, hR⟩ | ⟨h1, h2, hU, hR⟩ | ⟨h1, h2, hU, hR⟩
  · rw [hU]; refine ⟨by norm_num, fun h => by norm_num at h⟩
  · rw [hU, hR]
    refine ⟨by nlinarith [sq_nonneg (w.wU - 5)], fun _ => by nlinarith [sq_nonneg (w.wE - 15 / 2)]⟩
  · rw [hU]
    have hlt : (w.wU / 2) * (w.wR - w.wU) < 25 / 4 := by
      rcases hu0.lt_or_eq with hpos | hz
      · have : (w.wU / 2) * (w.wR - w.wU) < (w.wU / 2) * ((10 - w.wU) / 2) :=
          mul_lt_mul_of_pos_left (by linarith) (by linarith)
        nlinarith [sq_nonneg (w.wU - 5)]
      · rw [← hz]; norm_num
    exact ⟨hlt.le, fun h => absurd h (not_le.mpr hlt)⟩

end CSProp2Dis

open CSProp2Dis in
theorem solution : ¬ (∀ (P : Params) (hP : P.Standing) (h : P.psi2 < P.cR),
    P.IsEquilibrium 1 P.priceI ∧ ∀ w, P.IsEquilibrium 1 w →
      P.Contingent 1 w ∧ w.wU = P.priceI.wU ∧ w.wE = (P.m + P.cR) / 2 ∧
      (P.psi1 < P.cR → P.P1 * w.wU + P.P0 * w.wE ≤ w.wR) ∧
      (P.cR ≤ P.psi1 → w.wR = P.P1 * w.wU + P.P0 * w.wE)) := by
  intro H
  have hP : P.Standing := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [P]
  have hpsi2 : P.psi2 < P.cR := by norm_num [P, Params.psi2, Params.P0]
  have hpsi1 : P.cR ≤ P.psi1 := by norm_num [P, Params.psi1]
  -- the profile (5, 7, 15/2): contingent sourcing with w_R strictly above η₂ = 25/4
  let w : Prices := ⟨5, 7, 15 / 2⟩
  have hpw : P.payU 1 w = 25 / 4 ∧ P.payR 1 w = 25 / 16 := by
    rcases pay_cases w with ⟨h1, -, -⟩ | ⟨-, -, hU, hR⟩ | ⟨-, h2, -, -⟩
    · norm_num [w] at h1
    · rw [hU, hR]; norm_num [w]
    · norm_num [w] at h2
  have hNash : P.IsNash 1 w := by
    refine ⟨⟨by norm_num [P, w], by norm_num [P, w]⟩, ⟨by norm_num [P, w], by norm_num [w],
      by norm_num [P, w]⟩, ?_, ?_⟩
    · intro wR' wE' ⟨h1, h2, h3⟩
      rw [hpw.2]
      change 5 ≤ wR' at h1; change wE' ≤ 10 at h3
      rcases pay_cases ⟨5, wR', wE'⟩ with ⟨a1, -, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, -, hR⟩
      · rw [hR]; try dsimp only at a1 ⊢
        have : wR' = 5 := by linarith
        rw [this]; norm_num
      · rw [hR]; try dsimp only; nlinarith [sq_nonneg (wE' - 15 / 2)]
      · rw [hR]; try dsimp only; nlinarith [sq_nonneg (wR' - 25 / 4)]
    · intro wU' ⟨h1, h2⟩
      rw [hpw.1]
      have h1' : 0 ≤ wU' := by simpa [P] using h1
      have h2' : wU' ≤ 10 := by simpa [P] using h2
      exact (bounds ⟨wU', 7, 15 / 2⟩ h1' h2' (by norm_num) (by norm_num) (by norm_num)).1
  have hEq : P.IsEquilibrium 1 w := by
    refine ⟨hNash, ?_⟩
    rintro ⟨w'', hN'', hU'', hR'', hstrict⟩
    obtain ⟨⟨u1, u2⟩, ⟨r1, r2, r3⟩, -, -⟩ := hN''
    have hu1 : 0 ≤ w''.wU := by simpa [P] using u1
    have hu2 : w''.wU ≤ 10 := by simpa [P] using u2
    have hr1 : 5 ≤ w''.wR := by simpa [P] using r1
    have hr3 : w''.wE ≤ 10 := by simpa [P] using r3
    obtain ⟨bU, bR⟩ := bounds w'' hu1 hu2 hr1 r2 hr3
    rw [hpw.1, hpw.2] at *
    have hR' := bR hU''
    rcases hstrict with h | h <;> linarith
  obtain ⟨-, hall⟩ := H P hP hpsi2
  obtain ⟨-, -, -, -, hwR⟩ := hall w hEq
  have := hwR hpsi1
  norm_num [w, P, Params.P0] at this
