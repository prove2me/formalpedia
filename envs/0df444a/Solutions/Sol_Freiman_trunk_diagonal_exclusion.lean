-- Prove2me | solution 1 for Freiman.trunk_diagonal_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:37.743302+00:00
-- url     : https://prove2.me/submissions/f9f9c58e-c3ac-45dc-b32b-cdace6826c6c

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Theorems.Thm_Freiman_trunk_diagonal_polynomial
import Theorems.Thm_Freiman_trunk_diagonal_denominators
import Theorems.Thm_Freiman_cert_cross_polynomial
import Theorems.Thm_Freiman_cert_threshold_cross_order
import Theorems.Thm_Freiman_cert_bound_pair_incompatible

open Freiman

theorem solution (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) (hn : w.diagonal ≠ 0) :
    TrunkWitnessExclusion C w := by
  intro l u hu r s q hm hs
  have hp := trunk_diagonal_polynomial C w hw hn r s hm (hs.resolve_left hn)
  have hd := trunk_diagonal_denominators C w hw hn r s hm
  have hl := hu.2.2.1
  have hr := hu.2.2.2.1
  have hstrict : l.strict = true ∨ u.strict = true := by
    rcases hu.2.2.2.2 with h | h
    · exact False.elim (hn h.1)
    · exact h
  change 0 ≤ certPolyEval (certCrossPolynomial _ _) r s at hp
  have hp' : 0 ≤ certPolyEval (certCrossPolynomial l.threshold u.threshold) r s := by
    simpa only [hl,hr] using hp
  have dl : 0 < certThresholdDen l.threshold r := by simpa only [hl] using hd.1
  have du : 0 < certThresholdDen u.threshold r := by simpa only [hr] using hd.2
  rw [cert_cross_polynomial l.threshold u.threshold r s] at hp'
  have ho := (cert_threshold_cross_order _ _ r s dl du).1.mp hp'
  exact cert_bound_pair_incompatible l u r s q hu.1 hu.2.1 (Or.inr ⟨ho,hstrict⟩)
