-- Prove2me | solution 1 for CachonCoord.Proportional.coordination_price
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:05:21.686027+00:00
-- url     : https://prove2.me/submissions/811dce05-9521-4b77-885e-af75be023a32

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

set_option autoImplicit false

open CachonCoord.Proportional in
lemma cc7a_avgF_bounds (M : Model) (q : ℝ) (hq : 0 < q) :
    0 ≤ M.avgF q ∧ M.avgF q ≤ M.F q := by
  have hmono : Monotone M.F := ProbabilityTheory.monotone_cdf M.law
  have hint : IntervalIntegrable M.F MeasureTheory.volume 0 q := hmono.intervalIntegrable
  have h0 : 0 ≤ ∫ x in (0 : ℝ)..q, M.F x :=
    intervalIntegral.integral_nonneg hq.le (fun u _ => ProbabilityTheory.cdf_nonneg M.law u)
  have h1 : (∫ x in (0 : ℝ)..q, M.F x) ≤ ∫ x in (0 : ℝ)..q, M.F q :=
    intervalIntegral.integral_mono_on hq.le hint intervalIntegrable_const
      (fun x hx => hmono hx.2)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
  unfold CachonCoord.Proportional.Model.avgF
  constructor
  · exact mul_nonneg (by positivity) h0
  · rw [one_div, inv_mul_le_iff₀ hq]
    exact h1

open CachonCoord.Proportional in
theorem solution (M : Model) (n : ℕ) (hn : 2 ≤ n) (b qo : ℝ) (hb : b < M.p)
    (hqo : M.F qo = (M.p - M.c) / M.p) :
    M.lhs22 n qo = (M.p - M.wb n b qo) / (M.p - b) ∧
      b < M.wb n b qo ∧ M.wb n b qo < M.p ∧
      (0 < b → M.what n qo < M.wb n b qo) := by
  have hc := M.c_pos
  have hcp := M.c_lt_p
  have hp : 0 < M.p := by linarith
  have hF0 : 0 < M.F qo := by rw [hqo]; exact div_pos (by linarith) hp
  have hF1 : M.F qo < 1 := by
    rw [hqo, div_lt_one hp]; linarith
  have hqpos : 0 < qo := by
    by_contra h
    push_neg at h
    have h2 : M.F qo ≤ M.F 0 := ProbabilityTheory.monotone_cdf M.law h
    have h3 : M.F 0 = 0 := M.cdf_zero
    linarith
  obtain ⟨hA0, hA1⟩ := cc7a_avgF_bounds M qo hqpos
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set L := M.lhs22 n qo with hL
  set A := M.avgF qo with hA
  have hLdef : L = (1 / (n : ℝ)) * ((M.p - M.c) / M.p) + (((n : ℝ) - 1) / (n : ℝ)) * A := by
    rw [hL]; unfold CachonCoord.Proportional.Model.lhs22; rw [hqo]
  have hwb : M.wb n b qo = M.p - (M.p - b) * L := by
    rw [hLdef]; rfl
  have hwhat : M.what n qo = M.p * (1 - L) := by
    rw [hL]; unfold CachonCoord.Proportional.Model.what CachonCoord.Proportional.Model.lhs22
    ring
  have hLpos : 0 < L := by
    rw [hL]; unfold CachonCoord.Proportional.Model.lhs22
    have : 0 ≤ (((n : ℝ) - 1) / (n : ℝ)) * M.avgF qo :=
      mul_nonneg (div_nonneg (by linarith) hnpos.le) hA0
    have : 0 < (1 / (n : ℝ)) * M.F qo := mul_pos (by positivity) hF0
    linarith
  have hLlt : L < 1 := by
    have hle : L ≤ M.F qo := by
      rw [hL]; unfold CachonCoord.Proportional.Model.lhs22
      have e : M.F qo = (1 / (n : ℝ)) * M.F qo + (((n : ℝ) - 1) / (n : ℝ)) * M.F qo := by
        field_simp; ring
      have : (((n : ℝ) - 1) / (n : ℝ)) * M.avgF qo ≤ (((n : ℝ) - 1) / (n : ℝ)) * M.F qo :=
        mul_le_mul_of_nonneg_left hA1 (div_nonneg (by linarith) hnpos.le)
      linarith
    linarith
  have hpb : 0 < M.p - b := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hwb, eq_div_iff hpb.ne']; ring
  · rw [hwb]; nlinarith
  · rw [hwb]; nlinarith
  · intro hb0
    rw [hwb, hwhat]; nlinarith
