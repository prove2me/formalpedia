-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.oddExponentCount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:26.70189+00:00
-- url     : https://prove2.me/submissions/4c35641a-b809-4979-93a8-66751a489b72

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : JCount := by
  intro l a hl ha
  set L := Nat.log l a with hLdef
  have hsub : (Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a) ⊆
      Finset.Icc (-(L : ℤ)) L := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    have h1 : j.natAbs ≤ L := Nat.le_log_of_pow_le (by omega) hj.2.2
    rcases Int.natAbs_eq j with h | h <;> omega
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have h2 : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
  rw [h2] at hcard
  have hL : (L : ℝ) ≤ Real.logb l a := Real.natLog_le_logb a l
  have h3 : ((((Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a)).card : ℕ) : ℝ)
      ≤ ((2 * L + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  push_cast at h3
  linarith
end Formalism.DworkPowerSeriesWeights
