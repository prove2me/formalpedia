-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.least_odd_top_level_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:37.395805+00:00
-- url     : https://prove2.me/submissions/1b055bdf-92db-4ef5-b0f2-cecce0aa22df

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementN
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CompanionTheory

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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution {d : ℕ} [NeZero d] (TT : Finset (ZMod d)) (s : ZMod d) (e : ℕ)
    (h : dTop d TT s = (e : ℕ∞)) :
    (Odd e ∧ s + (e : ZMod d) ∈ TT) ∧ ∀ e' : ℕ, Odd e' → s + (e' : ZMod d) ∈ TT → e ≤ e' := by
  classical
  have hex : ∃ e' : ℕ, Odd e' ∧ s + (e' : ZMod d) ∈ TT := by
    by_contra hne
    push_neg at hne
    have htop : dTop d TT s = ⊤ := by
      unfold dTop
      simp only [iInf_eq_top]
      intro e' he'
      exact absurd he'.2 (hne e' he'.1)
    rw [htop] at h
    first
    | exact ENat.top_ne_coe e h
    | simp at h
  have hle : ∀ e' : ℕ, Odd e' → s + (e' : ZMod d) ∈ TT → dTop d TT s ≤ (e' : ℕ∞) := by
    intro e' h1 h2
    unfold dTop
    exact iInf₂_le e' ⟨h1, h2⟩
  have hfind : dTop d TT s = ((Nat.find hex : ℕ) : ℕ∞) := by
    apply le_antisymm
    · exact hle _ (Nat.find_spec hex).1 (Nat.find_spec hex).2
    · unfold dTop
      apply le_iInf₂
      intro e' he'
      exact_mod_cast Nat.find_min' hex he'
  have he : e = Nat.find hex := by
    rw [h] at hfind
    exact_mod_cast hfind
  refine ⟨?_, ?_⟩
  · rw [he]
    exact Nat.find_spec hex
  · intro e' h1 h2
    have h3 := hle e' h1 h2
    rw [h] at h3
    exact_mod_cast h3
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
