-- Prove2me | solution 1 for ContingentSourcing.Competition.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:30:59.007803+00:00
-- url     : https://prove2.me/submissions/069efd72-3b40-464a-bb4c-3ab0625894da

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

open ContingentSourcing.Competition

namespace CSProp1Aux

lemma rev_le (P : Params) (c x : ℝ) (hc : 0 ≤ c) (hx : 0 ≤ x) :
    P.revenue x - c * x ≤ (P.m - c) ^ 2 / 4 := by
  unfold Params.revenue
  split_ifs with h
  · nlinarith [sq_nonneg (2 * x - (P.m - c))]
  · push_neg at h; nlinarith [sq_nonneg c]

lemma rev_at (P : Params) (c : ℝ) (hc : 0 ≤ c) :
    P.revenue ((P.m - c) / 2) - c * ((P.m - c) / 2) = (P.m - c) ^ 2 / 4 := by
  unfold Params.revenue
  rw [if_pos (by linarith)]; ring

lemma PG_pos (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ1 : ρ ≤ 1) : 0 < P.PG ρ := by
  obtain ⟨hm, hp0, hp1, -⟩ := hP
  unfold Params.PG Params.P0
  nlinarith

/-- The objective (2) as a convex combination of the three states. -/
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

/-- Lagrangian decomposition of the objective with state prices cA, cS, cT. -/
lemma profit_decomp (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ1 : ρ ≤ 1) (w : Prices) (q : Orders)
    (cA cS cT : ℝ) :
    P.buyerProfit ρ w q =
      (1 - P.P1) * ρ * (P.revenue (q.QR + q.QEB) - cA * (q.QR + q.QEB))
      + (1 - P.P1) * (1 - ρ) * (P.revenue (q.QR + q.QEG) - cS * (q.QR + q.QEG))
      + P.P1 * (P.revenue (q.QU + q.QR + q.QEG) - cT * (q.QU + q.QR + q.QEG))
      + q.QR * ((1 - P.P1) * ρ * cA + (1 - P.P1) * (1 - ρ) * cS + P.P1 * cT - w.wR)
      + (1 - P.P1) * ρ * q.QEB * (cA - w.wE)
      + q.QEG * ((1 - P.P1) * (1 - ρ) * cS + P.P1 * cT - ((1 - P.P1) * (1 - ρ) + P.P1) * w.wE)
      + P.P1 * q.QU * (cT - w.wU) := by
  rw [profit_eq P hP ρ hρ1]; ring

lemma profit_le (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (w : Prices)
    (cA cS cT : ℝ) (hA : 0 ≤ cA) (hS : 0 ≤ cS) (hT : 0 ≤ cT)
    (kR : (1 - P.P1) * ρ * cA + (1 - P.P1) * (1 - ρ) * cS + P.P1 * cT ≤ w.wR)
    (kEB : cA ≤ w.wE)
    (kEG : (1 - P.P1) * (1 - ρ) * cS + P.P1 * cT ≤ ((1 - P.P1) * (1 - ρ) + P.P1) * w.wE)
    (kU : cT ≤ w.wU) (q : Orders) (hq : q.Feasible) :
    P.buyerProfit ρ w q ≤ (1 - P.P1) * ρ * ((P.m - cA) ^ 2 / 4)
      + (1 - P.P1) * (1 - ρ) * ((P.m - cS) ^ 2 / 4) + P.P1 * ((P.m - cT) ^ 2 / 4) := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hp0 := hP.2.1; have hp1 := hP.2.2.1
  rw [profit_decomp P hP ρ hρ1 w q cA cS cT]
  have ha : 0 ≤ (1 - P.P1) * ρ := mul_nonneg (by linarith) hρ0
  have hb : 0 ≤ (1 - P.P1) * (1 - ρ) := mul_nonneg (by linarith) (by linarith)
  have r1 := mul_le_mul_of_nonneg_left (rev_le P cA (q.QR + q.QEB) hA (by linarith)) ha
  have r2 := mul_le_mul_of_nonneg_left (rev_le P cS (q.QR + q.QEG) hS (by linarith)) hb
  have r3 := mul_le_mul_of_nonneg_left (rev_le P cT (q.QU + q.QR + q.QEG) hT (by linarith)) hp0.le
  have s1 := mul_nonpos_of_nonneg_of_nonpos h2 (by linarith : (1 - P.P1) * ρ * cA
    + (1 - P.P1) * (1 - ρ) * cS + P.P1 * cT - w.wR ≤ 0)
  have s2 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha h4) (by linarith : cA - w.wE ≤ 0)
  have s3 := mul_nonpos_of_nonneg_of_nonpos h3 (by linarith : (1 - P.P1) * (1 - ρ) * cS + P.P1 * cT
    - ((1 - P.P1) * (1 - ρ) + P.P1) * w.wE ≤ 0)
  have s4 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hp0.le h1) (by linarith : cT - w.wU ≤ 0)
  linarith

lemma profit_at (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ1 : ρ ≤ 1) (w : Prices) (q : Orders)
    (cA cS cT : ℝ) (hA : 0 ≤ cA) (hS : 0 ≤ cS) (hT : 0 ≤ cT)
    (eA : q.QR + q.QEB = (P.m - cA) / 2) (eS : q.QR + q.QEG = (P.m - cS) / 2)
    (eT : q.QU + q.QR + q.QEG = (P.m - cT) / 2)
    (z1 : q.QR * ((1 - P.P1) * ρ * cA + (1 - P.P1) * (1 - ρ) * cS + P.P1 * cT - w.wR) = 0)
    (z2 : (1 - P.P1) * ρ * q.QEB * (cA - w.wE) = 0)
    (z3 : q.QEG * ((1 - P.P1) * (1 - ρ) * cS + P.P1 * cT - ((1 - P.P1) * (1 - ρ) + P.P1) * w.wE) = 0)
    (z4 : P.P1 * q.QU * (cT - w.wU) = 0) :
    P.buyerProfit ρ w q = (1 - P.P1) * ρ * ((P.m - cA) ^ 2 / 4)
      + (1 - P.P1) * (1 - ρ) * ((P.m - cS) ^ 2 / 4) + P.P1 * ((P.m - cT) ^ 2 / 4) := by
  rw [profit_decomp P hP ρ hρ1 w q cA cS cT, z1, z2, z3, z4, eA, eS, eT,
    rev_at P cA hA, rev_at P cS hS, rev_at P cT hT]
  ring

lemma optimal_of (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (w : Prices)
    (q : Orders) (hq : q.Feasible)
    (cA cS cT : ℝ) (hA : 0 ≤ cA) (hS : 0 ≤ cS) (hT : 0 ≤ cT)
    (kR : (1 - P.P1) * ρ * cA + (1 - P.P1) * (1 - ρ) * cS + P.P1 * cT ≤ w.wR)
    (kEB : cA ≤ w.wE)
    (kEG : (1 - P.P1) * (1 - ρ) * cS + P.P1 * cT ≤ ((1 - P.P1) * (1 - ρ) + P.P1) * w.wE)
    (kU : cT ≤ w.wU)
    (eA : q.QR + q.QEB = (P.m - cA) / 2) (eS : q.QR + q.QEG = (P.m - cS) / 2)
    (eT : q.QU + q.QR + q.QEG = (P.m - cT) / 2)
    (z1 : q.QR * ((1 - P.P1) * ρ * cA + (1 - P.P1) * (1 - ρ) * cS + P.P1 * cT - w.wR) = 0)
    (z2 : (1 - P.P1) * ρ * q.QEB * (cA - w.wE) = 0)
    (z3 : q.QEG * ((1 - P.P1) * (1 - ρ) * cS + P.P1 * cT - ((1 - P.P1) * (1 - ρ) + P.P1) * w.wE) = 0)
    (z4 : P.P1 * q.QU * (cT - w.wU) = 0) :
    P.IsOptimalOrder ρ w q := by
  refine ⟨hq, fun q' hq' => ?_⟩
  rw [profit_at P hP ρ hρ1 w q cA cS cT hA hS hT eA eS eT z1 z2 z3 z4]
  exact profit_le P hP ρ hρ0 hρ1 w cA cS cT hA hS hT kR kEB kEG kU q' hq'


lemma PGP0G (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ1 : ρ ≤ 1) :
    P.PG ρ * P.P0G ρ = (1 - P.P1) * (1 - ρ) := by
  have h := (PG_pos P hP ρ hρ1).ne'
  unfold Params.P0G; field_simp; unfold Params.P0; ring

lemma eta1_eq (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ1 : ρ ≤ 1) (w : Prices) :
    P.eta1 ρ w = P.P1 * w.wU + (1 - P.P1) * ρ * w.wE + (1 - P.P1) * (1 - ρ) * P.m := by
  unfold Params.eta1; rw [PGP0G P hP ρ hρ1]; unfold Params.PB Params.P0; ring

end CSProp1Aux

open CSProp1Aux in
theorem solution (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (w : Prices) (hwU0 : 0 ≤ w.wU) (hwUm : w.wU ≤ P.m) (hwR0 : 0 ≤ w.wR) (hRE : w.wR ≤ w.wE)
    (hwEm : w.wE ≤ P.m) :
    (P.eta1 ρ w < w.wR → P.IsOptimalOrder ρ w (P.orderI w)) ∧
    (P.eta2 w < w.wR → w.wR ≤ P.eta1 ρ w → P.IsOptimalOrder ρ w (P.orderII ρ w)) ∧
    (w.wU < w.wR → w.wR ≤ P.eta2 w → P.IsOptimalOrder ρ w (P.orderIII w)) ∧
    (w.wR ≤ w.wU → P.IsOptimalOrder ρ w (P.orderIV w)) := by
  have hp0 := hP.2.1; have hp1 := hP.2.2.1
  have hq : 0 < 1 - P.P1 := by linarith
  have ha : 0 ≤ (1 - P.P1) * ρ := mul_nonneg hq.le hρ0
  have hb : 0 ≤ (1 - P.P1) * (1 - ρ) := mul_nonneg hq.le (by linarith)
  have heta1 := eta1_eq P hP ρ hρ1 w
  have heta2 : P.eta2 w = P.P1 * w.wU + (1 - P.P1) * w.wE := by unfold Params.eta2 Params.P0; ring
  refine ⟨fun h => ?_, fun h2 h1 => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · -- contingent
    rw [heta1] at h
    have hab : (1 - P.P1) * (1 - ρ) * P.m + P.P1 * w.wU ≤ ((1 - P.P1) * (1 - ρ) + P.P1) * w.wE := by
      have : (1 - P.P1) * ρ * w.wE + ((1 - P.P1) * (1 - ρ) + P.P1) * w.wE = w.wE := by ring
      linarith
    refine optimal_of P hP ρ hρ0 hρ1 w _ ?feas1 w.wE P.m w.wU (by linarith) (by linarith) hwU0
      (by linarith) le_rfl (by linarith) le_rfl ?eA1 ?eS1 ?eT1 ?z11 ?z21 ?z31 ?z41
    case feas1 => exact ⟨by simp only [Params.orderI]; linarith, le_rfl, le_rfl,
      by simp only [Params.orderI]; linarith⟩
    all_goals simp only [Params.orderI]; ring
  · -- mixed
    rw [heta1] at h1; rw [heta2] at h2
    have hρ : ρ < 1 := by
      rcases hρ1.lt_or_eq with h | h
      · exact h
      · exfalso; subst h; nlinarith
    have hb' : 0 < (1 - P.P1) * (1 - ρ) := mul_pos hq (by linarith)
    have hq1 : (1 - ρ) ≠ 0 := by intro h; linarith
    have hq2 : (1 - P.P1) ≠ 0 := hq.ne'
    have hwE0 : 0 ≤ w.wE := by linarith
    have hUR : w.wU < w.wR := by
      by_contra hc; push_neg at hc
      have : P.P1 * w.wR + (1 - P.P1) * w.wR ≤ P.P1 * w.wU + (1 - P.P1) * w.wE := by
        have := mul_le_mul_of_nonneg_left hc hp0.le
        have := mul_le_mul_of_nonneg_left hRE hq.le
        linarith
      linarith
    have hPG : P.PG ρ = 1 - (1 - P.P1) * ρ := by unfold Params.PG Params.P0; ring
    have hPB : P.PB ρ = (1 - P.P1) * ρ := by unfold Params.PB Params.P0; ring
    have hO : P.orderII ρ w = ⟨(w.wR - (1 - (1 - P.P1) * ρ) * w.wU - (1 - P.P1) * ρ * w.wE) /
        (2 * ((1 - P.P1) * (1 - ρ))),
        ((1 - P.P1) * (1 - ρ) * P.m - w.wR + (1 - P.P1) * ρ * w.wE + P.P1 * w.wU) /
        (2 * ((1 - P.P1) * (1 - ρ))), 0,
        (w.wR - P.P1 * w.wU - (1 - P.P1) * w.wE) / (2 * ((1 - P.P1) * (1 - ρ)))⟩ := by
      unfold Params.orderII
      rw [mul_assoc 2, PGP0G P hP ρ hρ1, hPG, hPB]; unfold Params.P0; rfl
    rw [hO]
    have hcS : 0 ≤ (w.wR - (1 - P.P1) * ρ * w.wE - P.P1 * w.wU) / ((1 - P.P1) * (1 - ρ)) := by
      apply div_nonneg _ hb'.le
      have : (1 - P.P1) * ρ * w.wE ≤ (1 - P.P1) * w.wE := by
        have := mul_le_mul_of_nonneg_left hρ1 (mul_nonneg hq.le hwE0); nlinarith
      linarith
    have hbc : (1 - P.P1) * (1 - ρ) * ((w.wR - (1 - P.P1) * ρ * w.wE - P.P1 * w.wU) /
        ((1 - P.P1) * (1 - ρ))) = w.wR - (1 - P.P1) * ρ * w.wE - P.P1 * w.wU := by
      field_simp
    refine optimal_of P hP ρ hρ0 hρ1 w _ ?feas2 w.wE
      ((w.wR - (1 - P.P1) * ρ * w.wE - P.P1 * w.wU) / ((1 - P.P1) * (1 - ρ))) w.wU hwE0
      hcS hwU0 ?kR2 le_rfl ?kEG2 le_rfl ?eA2 ?eS2 ?eT2 ?z12 ?z22 ?z32 ?z42
    case feas2 =>
      refine ⟨?_, ?_, le_rfl, ?_⟩ <;> simp only <;> apply div_nonneg _ (by linarith)
      · have : 0 ≤ (1 - P.P1) * (1 - ρ) * (w.wE - w.wU) := mul_nonneg hb (by linarith)
        nlinarith
      · linarith
      · linarith
    case kR2 => rw [hbc]; linarith
    case kEG2 =>
      rw [hbc]
      have : (1 - P.P1) * ρ * w.wE + ((1 - P.P1) * (1 - ρ) + P.P1) * w.wE = w.wE := by ring
      linarith
    case z12 => simp only; rw [hbc]; ring
    all_goals simp only; field_simp; ring
  · -- diversification
    rw [heta2] at h2
    have hqne := hq.ne'
    have hcs : 0 ≤ (w.wR - P.P1 * w.wU) / (1 - P.P1) := by
      apply div_nonneg _ hq.le
      have := mul_le_mul_of_nonneg_left hwU0 hp0.le
      nlinarith
    have hcE : (w.wR - P.P1 * w.wU) / (1 - P.P1) ≤ w.wE := by
      rw [div_le_iff₀ hq]; linarith
    have hcR : (1 - P.P1) * ((w.wR - P.P1 * w.wU) / (1 - P.P1)) = w.wR - P.P1 * w.wU := by
      field_simp
    refine optimal_of P hP ρ hρ0 hρ1 w _ ?feas3 _ _ w.wU hcs hcs hwU0 ?kR3 hcE ?kEG3 le_rfl
      ?eA3 ?eS3 ?eT3 ?z13 ?z23 ?z33 ?z43
    case feas3 =>
      refine ⟨?_, ?_, le_rfl, le_rfl⟩ <;> simp only [Params.orderIII, Params.P0] <;>
        apply div_nonneg _ (by linarith)
      · linarith
      · have := mul_le_mul_of_nonneg_left hwEm hq.le; linarith
    case kR3 =>
      have : (1 - P.P1) * ρ * ((w.wR - P.P1 * w.wU) / (1 - P.P1)) + (1 - P.P1) * (1 - ρ) *
          ((w.wR - P.P1 * w.wU) / (1 - P.P1)) = (1 - P.P1) * ((w.wR - P.P1 * w.wU) / (1 - P.P1)) := by
        ring
      rw [hcR] at this; linarith
    case kEG3 =>
      have h1' : w.wU ≤ w.wE := by linarith
      have := mul_le_mul_of_nonneg_left hcE hb
      have := mul_le_mul_of_nonneg_left h1' hp0.le
      linarith
    case z13 =>
      simp only [Params.orderIII]
      have : (1 - P.P1) * ρ * ((w.wR - P.P1 * w.wU) / (1 - P.P1)) + (1 - P.P1) * (1 - ρ) *
          ((w.wR - P.P1 * w.wU) / (1 - P.P1)) + P.P1 * w.wU - w.wR = 0 := by
        field_simp; ring
      rw [this, mul_zero]
    all_goals simp only [Params.orderIII, Params.P0]; field_simp; ring
  · -- sole sourcing from R
    refine optimal_of P hP ρ hρ0 hρ1 w _ ?feas4 w.wR w.wR w.wR hwR0 hwR0 hwR0 ?kR4 hRE ?kEG4 h
      ?eA4 ?eS4 ?eT4 ?z14 ?z24 ?z34 ?z44
    case feas4 => exact ⟨le_rfl, by simp only [Params.orderIV]; linarith, le_rfl, le_rfl⟩
    case kR4 => ring_nf; linarith
    case kEG4 =>
      have := mul_le_mul_of_nonneg_left hRE (add_nonneg hb hp0.le)
      linarith
    all_goals simp only [Params.orderIV]; ring
