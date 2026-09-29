-- Prove2me | solution 1 for Freiman.trunk_boundary_corner_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:54:21.119267+00:00
-- url     : https://prove2.me/submissions/576465de-8697-43f9-8e95-28cdb10f6640

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

import Theorems.Thm_Freiman_cert_threshold_denominator_positive
import Theorems.Thm_Freiman_cert_field_lower_bound
import Theorems.Thm_Freiman_cert_field_sub
import Theorems.Thm_Freiman_cert_field_mul
import Theorems.Thm_Freiman_cert_field_add
import Theorems.Thm_Freiman_cert_field_scale
open Freiman
theorem solution (R : CertRectangle) (bs : List CertBound) (hb : trunkBoundaryBound R bs)
    (r s q : ℝ) (hm : certRectangleMem R r s) (hrs : r = s) (h : trunkHolds bs r s q) :
    False := by
  have hr : 0 ≤ r := le_trans (by exact_mod_cast hb.1) hm.1
  subst s
  rcases hb with ⟨_, _, hcorner, _, ⟨u, hu, hul, hut⟩, b, hbm, hbl, hbt, hdiff⟩
  have hra : r = (R.r1 : ℝ) := by
    have hc : (R.r1 : ℝ) = (R.s0 : ℝ) := by exact_mod_cast hcorner
    linarith [hm.2.1, hm.2.2.1]
  have hden (t : CertThreshold) (ht : certThresholdDataValid t) :
      0 < certThresholdDen t r := by
    apply cert_threshold_denominator_positive t r hr
    · exact le_trans (by exact_mod_cast ht.1) (cert_field_lower_bound _)
    · exact le_trans (by exact_mod_cast ht.2) (cert_field_lower_bound _)
  have hrat : certFieldVal (lowerHistoryRat 1) = 1 := by norm_num [lowerHistoryRat, certFieldVal]
  have he : certFieldVal (trunkThresholdOneDifference b.threshold R.r1) =
      certThresholdNum b.threshold r - certThresholdDen b.threshold r := by
    simp only [trunkThresholdOneDifference, cert_field_sub, cert_field_mul,
      cert_field_add, cert_field_scale, hrat, certThresholdNum, certThresholdDen, hra]
    ring
  have hdiffReal : 0 < certThresholdNum b.threshold r - certThresholdDen b.threshold r := by
    rw [← he]
    exact lt_of_lt_of_le (by exact_mod_cast hdiff) (cert_field_lower_bound _)
  have hbval : 1 < certThresholdVal b.threshold r r := by
    unfold certThresholdVal
    apply (lt_div_iff₀ (hden _ hbt)).2
    linarith
  have hbq : certThresholdVal b.threshold r r ≤ q := by
    have hh := h b hbm
    cases hs : b.strict <;>
      simp only [certBoundHolds, hbl, hs, Bool.false_eq_true, if_true, if_false] at hh <;>
      linarith
  have huq : q ≤ certThresholdVal (lowerHistoryWH ([],[])) r r := by
    have hh := h u hu
    cases hs : u.strict <;>
      simp only [certBoundHolds, hul, hs, hut, Bool.false_eq_true, if_true, if_false] at hh <;>
      linarith
  have hz : lowerHistoryWH ([],[]) =
      ⟨⟨1,0,0,0⟩,lowerHistoryBeta,lowerHistoryAlpha,lowerHistoryBeta,lowerHistoryAlpha⟩ := by
    norm_num [lowerHistoryWH, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs,
      lowerHistoryDiv, lowerHistoryInv, lowerHistoryCF, lowerHistoryMatrix,
      lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryRat, lowerHistoryNeg,
      lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, certFieldSub,
      certFieldAdd, certFieldScale, certFieldMul]
  have hzd : certThresholdDataValid (lowerHistoryWH ([],[])) := by
    unfold certThresholdDataValid
    decide +kernel
  have hsame : certThresholdNum (lowerHistoryWH ([],[])) r = certThresholdDen (lowerHistoryWH ([],[])) r := by
    rw [hz]
    simp [certThresholdNum, certThresholdDen, certFieldVal]
  have hone : certThresholdVal (lowerHistoryWH ([],[])) r r = 1 := by
    unfold certThresholdVal
    rw [hsame, div_self (ne_of_gt (hden _ hzd))]
  rw [hone] at huq
  linarith
