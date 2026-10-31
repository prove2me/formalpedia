-- Prove2me | solution 1 for ContingentSourcing.Competition.proposition_3_i_ii
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:36:10.592224+00:00
-- url     : https://prove2.me/submissions/296bcb55-de32-4069-b922-61b95bf2e410

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

open ContingentSourcing.Competition

theorem solution : ¬ (∀ (P : Params) (hP : P.Standing) (h : P.psi3 < P.cR),
    P.IsEquilibrium 0 P.priceN ∧ ∀ w, P.IsEquilibrium 0 w →
      w.wU = P.priceN.wU ∧
      (P.phi2 < P.cR → (P.order 0 w).QR = 0 ∧ 0 < (P.order 0 w).QU) ∧
      (P.cR ≤ P.phi2 → w.wR = P.priceN.wR ∧ 0 < (P.order 0 w).QU ∧ 0 < (P.order 0 w).QR)) := by
  intro H
  let P : Params := ⟨10, 1 / 2, 0, 20 / 3⟩
  have hP : P.Standing := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [P]
  have hpsi3 : P.psi3 < P.cR := by norm_num [P, Params.psi3, Params.P0]
  have hphi2 : P.phi2 = 20 / 3 := by norm_num [P, Params.phi2, Params.P0]
  have hphi1 : P.phi1 = 15 / 2 := by norm_num [P, Params.phi1, Params.P0]
  have hpr : P.priceN = ⟨10 / 3, 20 / 3, 10⟩ := by
    unfold Params.priceN
    rw [if_neg (by rw [hphi1]; norm_num [P]), if_neg (by rw [hphi2]; norm_num [P])]
    simp only [Prices.mk.injEq]
    norm_num [P, Params.P0]
  obtain ⟨hEq, hall⟩ := H P hP hpsi3
  obtain ⟨-, -, hii⟩ := hall _ hEq
  obtain ⟨-, -, hQR⟩ := hii (by rw [hphi2])
  have hord : (P.order 0 P.priceN).QR = 0 := by
    rw [hpr]
    unfold Params.order
    have h1 : ¬ ((⟨10 / 3, 20 / 3, 10⟩ : Prices).wR ≤ (⟨10 / 3, 20 / 3, 10⟩ : Prices).wU) := by norm_num
    have h2 : P.eta1 0 ⟨10 / 3, 20 / 3, 10⟩ ≤ (⟨10 / 3, 20 / 3, 10⟩ : Prices).wR := by
      norm_num [Params.eta1, Params.PB, Params.PG, Params.P0G, Params.P0, P]
    rw [if_neg h1, if_pos h2]
    rfl
  rw [hord] at hQR
  exact lt_irrefl _ hQR
