-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_side_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:43.9534+00:00
-- url     : https://prove2.me/submissions/0d93b9e8-da3d-4470-a76e-acd580e413a6

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_choose_nonpow
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
open MvPowerSeries Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {d : ℕ} {l : ℕ} (hl : l.Prime) (P : ZMod d → Prop) (n : ZMod d →₀ ℕ)
    (h : ∃ s, P s ∧ n s ≠ 0) :
    (∃ s j, P s ∧ j < n s ∧ (0 < j ∨ ∃ t, P t ∧ t ≠ s ∧ n t ≠ 0) ∧ ¬ l ∣ (n s).choose j) ∨
    (∃ s e, P s ∧ (∀ t, P t → t ≠ s → n t = 0) ∧ n s = l ^ e) := by
  obtain ⟨s, hs, hns⟩ := h
  by_cases hex : ∃ t, P t ∧ t ≠ s ∧ n t ≠ 0
  · left
    refine ⟨s, 0, hs, Nat.pos_of_ne_zero hns, Or.inr hex, ?_⟩
    rw [Nat.choose_zero_right]
    exact hl.not_dvd_one
  · push_neg at hex
    by_cases hpow : ∃ e, n s = l ^ e
    · right
      obtain ⟨e, he⟩ := hpow
      exact ⟨s, e, hs, fun t ht hts => hex t ht hts, he⟩
    · left
      push_neg at hpow
      obtain ⟨j, hj0, hjn, hjd⟩ := bnx_choose_nonpow hl (n s) hns hpow
      exact ⟨s, j, hs, hjn, Or.inl hj0, hjd⟩
end Formalism.DworkPowerSeriesWeights
