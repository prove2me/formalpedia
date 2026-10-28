-- Prove2me | solution 1 for CycleLengthsExp.BetaGraph.condition_1_claim_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:35:45.542088+00:00
-- url     : https://prove2.me/submissions/c6abdce2-c6fb-4cb1-8fe6-cc10bd5b040d

import Mathlib
import Definitions.Def_CycleLengthsExp_BetaGraph_Setting

open CycleLengthsExp.BetaGraph in
theorem solution (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 20) (n : ℕ)
    (G : SimpleGraph (Fin n)) (hG : IsBetaGraph β G)
    (S : Set (Fin n)) (hSsize : (1 - β) * n ≤ S.ncard)
    (hS : ∀ U ⊆ S, (U.ncard : ℝ) ≤ β * n →
      (1 - 3 * β) / (2 * β) * U.ncard ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard)
    (U : Set (Fin n)) (hUS : U ⊆ S) (hU0 : 0 < U.ncard) (hU : (U.ncard : ℝ) ≤ β * n) :
    3 * U.ncard + 1 ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard := by
  have h := hS U hUS hU
  have h4 : (4 : ℝ) ≤ (1 - 3 * β) / (2 * β) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hu : (1 : ℝ) ≤ (U.ncard : ℝ) := by exact_mod_cast hU0
  have hx : (4 : ℝ) * U.ncard ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard := by
    nlinarith
  have : ((3 * U.ncard + 1 : ℕ) : ℝ) ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard := by
    push_cast
    linarith
  exact_mod_cast this
