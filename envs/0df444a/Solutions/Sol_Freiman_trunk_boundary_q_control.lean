-- Prove2me | solution 1 for Freiman.trunk_boundary_q_control
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:54:20.280693+00:00
-- url     : https://prove2.me/submissions/fee44a27-80e0-467c-9fc9-ee35ab71cbcd

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

import Theorems.Thm_Freiman_cert_threshold_denominator_positive
import Theorems.Thm_Freiman_cert_field_lower_bound
import Theorems.Thm_Freiman_cert_cross_polynomial
open Freiman
theorem solution (hc : trunkBoundaryCertificateValid) (R : CertRectangle) (bs : List CertBound)
    (hb : trunkBoundaryBound R bs) (r s q : ℝ) (hm : certRectangleMem R r s) (h : trunkHolds bs r s q) :
    certPolyEval trunkBoundaryPolynomial r s ≤ 0 := by
  have hr : 0 ≤ r := le_trans (by exact_mod_cast hb.1) hm.1
  rcases hb.2.2.2 with ⟨⟨l, hl, hll, hlt⟩, ⟨u, hu, hul, hut⟩, _⟩
  rcases hc with ⟨_, _, _, _, _, _, _, hld, hud⟩
  have hden (t : CertThreshold) (ht : certThresholdDataValid t) :
      0 < certThresholdDen t r := by
    apply cert_threshold_denominator_positive t r hr
    · exact le_trans (by exact_mod_cast ht.1) (cert_field_lower_bound _)
    · exact le_trans (by exact_mod_cast ht.2) (cert_field_lower_bound _)
  have hlq : certThresholdVal (lowerHistoryWH ([1],[1])) r s ≤ q := by
    have hh := h l hl
    cases hs : l.strict <;>
      simp only [certBoundHolds, hll, hs, hlt, Bool.false_eq_true, if_true, if_false] at hh <;>
      linarith
  have huq : q ≤ certThresholdVal (lowerHistoryWH ([],[])) r s := by
    have hh := h u hu
    cases hs : u.strict <;>
      simp only [certBoundHolds, hul, hs, hut, Bool.false_eq_true, if_true, if_false] at hh <;>
      linarith
  have horder := le_trans hlq huq
  unfold certThresholdVal at horder
  have hmul := (div_le_div_iff₀ (hden _ hld) (hden _ hud)).mp horder
  change certPolyEval (certCrossPolynomial (lowerHistoryWH ([1],[1])) (lowerHistoryWH ([],[]))) r s ≤ 0
  rw [cert_cross_polynomial]
  linarith only [hmul]
