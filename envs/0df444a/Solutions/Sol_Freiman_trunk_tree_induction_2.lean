-- Prove2me | solution 2 for Freiman.trunk_tree_induction
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:54:22.69019+00:00
-- url     : https://prove2.me/submissions/2e0becb7-26b3-41e5-b276-780e0ca97a26

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_cert_cross_polynomial
import Theorems.Thm_Freiman_cert_field_add
import Theorems.Thm_Freiman_cert_field_lower_bound
import Theorems.Thm_Freiman_cert_field_mul
import Theorems.Thm_Freiman_cert_field_scale
import Theorems.Thm_Freiman_cert_field_sub
import Theorems.Thm_Freiman_cert_threshold_denominator_positive
import Theorems.Thm_Freiman_trunk_boundary_polynomial_order

open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem scout_boundary_q_control (hc : trunkBoundaryCertificateValid) (R : CertRectangle) (bs : List CertBound)
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

theorem scout_boundary_corner_contra (R : CertRectangle) (bs : List CertBound) (hb : trunkBoundaryBound R bs)
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

theorem scout_boundary_exclusion (R : CertRectangle) (bs : List CertBound) (hb : trunkBoundaryBound R bs)
    (r s q : ℝ) (hm : certRectangleMem R r s) :
    ¬ trunkHolds bs r s q := by
  intro h
  have hc : trunkBoundaryCertificateValid := by
    unfold trunkBoundaryCertificateValid certThresholdDataValid
    decide +kernel
  have hr : 0 ≤ r := le_trans (by exact_mod_cast hb.1) hm.1
  have hs : 0 ≤ s := le_trans (by exact_mod_cast hb.2.1) hm.2.2.1
  have hrs : r ≤ s := by
    have he : (R.r1 : ℝ) = (R.s0 : ℝ) := by exact_mod_cast hb.2.2.1
    linarith [hm.2.1, hm.2.2.1]
  have hp := scout_boundary_q_control hc R bs hb r s q hm h
  have he := trunk_boundary_polynomial_order hc r s hr hs hrs hp
  exact scout_boundary_corner_contra R bs hb r s q hm he h

theorem scout_tree_induction_boundary (C : TrunkCatalog) (hw : trunkAllWitnesses C)
    (he : ∀ w : TrunkWitness, trunkWitnessValid C w → TrunkWitnessExclusion C w)
    (hs : ∀ (R : CertRectangle) (axis : Bool), certRectangleValid R → ∀ r s : ℝ, certRectangleMem R r s →
      (certRectangleValid (trunkRectangleHalf R axis false) ∧ certRectangleValid (trunkRectangleHalf R axis true)) ∧
      (certRectangleMem (trunkRectangleHalf R axis false) r s ∨ certRectangleMem (trunkRectangleHalf R axis true) r s))
    (hb : ∀ (R : CertRectangle) (bs : List CertBound), trunkBoundaryBound R bs → ∀ r s q : ℝ, certRectangleMem R r s → ¬ trunkHolds bs r s q) :
    TrunkTreeSound C := by
  have leaf (R : CertRectangle) (bs : List CertBound) (id : ℕ) (sign : ℤ)
      (ht : trunkLeafBound C R bs id sign) (r s q : ℝ)
      (hm : certRectangleMem R r s)
      (hside : sign = 0 ∨ 0 ≤ (sign : ℝ) * (r-s)) :
      ¬ trunkHolds bs r s q := by
    rcases ht with ⟨hid, hsize, hd, hcontains, l, hl, u, hu, huse⟩
    intro hholds
    have hvalid := hw id hid hsize
    have hmem : certRectangleMem (trunkWitness C id).rectangle r s := by
      rcases hcontains with ⟨hlo, hhi, hlo', hhi'⟩
      rcases hm with ⟨hr0, hr1, hs0, hs1⟩
      exact ⟨le_trans (by exact_mod_cast hlo) hr0,
        le_trans hr1 (by exact_mod_cast hhi),
        le_trans (by exact_mod_cast hlo') hs0,
        le_trans hs1 (by exact_mod_cast hhi')⟩
    exact he (trunkWitness C id) hvalid l u huse r s q hmem
      (by simpa only [hd] using hside) ⟨hholds l hl, hholds u hu⟩
  intro R bs tree
  induction tree generalizing R with
  | pair id =>
      intro _ ht r s q hm
      exact leaf R bs id 0 ht r s q hm (Or.inl rfl)
  | split axis left right ihl ihr =>
      intro hR ht r s q hm hholds
      obtain ⟨hvalid, hmem⟩ := hs R axis hR r s hm
      rcases hmem with hleft | hright
      · exact ihl _ hvalid.1 ht.1 r s q hleft hholds
      · exact ihr _ hvalid.2 ht.2 r s q hright hholds
  | diagonal negative positive =>
      intro _ ht r s q hm
      by_cases h : r ≤ s
      · exact leaf R bs negative (-1) ht.1 r s q hm (Or.inr (by norm_num; linarith))
      · exact leaf R bs positive 1 ht.2 r s q hm (Or.inr (by norm_num; linarith))
  | boundary =>
      intro _ ht r s q hm
      exact hb R bs ht r s q hm

theorem solution (C : TrunkCatalog) (hw : trunkAllWitnesses C)
    (he : ∀ w : TrunkWitness, trunkWitnessValid C w → TrunkWitnessExclusion C w)
    (hs : ∀ (R : CertRectangle) (axis : Bool), certRectangleValid R → ∀ r s : ℝ, certRectangleMem R r s →
      (certRectangleValid (trunkRectangleHalf R axis false) ∧ certRectangleValid (trunkRectangleHalf R axis true)) ∧
      (certRectangleMem (trunkRectangleHalf R axis false) r s ∨ certRectangleMem (trunkRectangleHalf R axis true) r s)) :
    TrunkTreeSound C := by
  exact scout_tree_induction_boundary C hw he hs scout_boundary_exclusion