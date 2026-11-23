-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.cap_le_odd_shift_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:46.849796+00:00
-- url     : https://prove2.me/submissions/8ae8fd10-d866-478b-af22-aa15b6708172

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_cap_values_bddAbove

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
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)
    (s : ZMod d) (j : ℤ) (hj : j < 0) (hodd : Odd j)
    (hsz : l ^ (-j).toNat ≤ Dl d TT nu1 size (s + (j : ZMod d))) :
    capL d TT nu1 nu2 (s + (j : ZMod d)) ≤ WcapOneLetter l d TT nu1 nu2 size s := by
  have hc : (((-j).toNat : ℕ) : ZMod d) = -((j : ZMod d)) := by
    have : (((-j).toNat : ℕ) : ℤ) = -j := Int.toNat_of_nonneg (by omega)
    rw [← Int.cast_natCast, this, Int.cast_neg]
  have hs : s - (((-j).toNat : ℕ) : ZMod d) = s + (j : ZMod d) := by
    rw [hc, sub_neg_eq_add]
  unfold WcapOneLetter
  apply le_csSup (cap_values_bddAbove d TT nu1 nu2 s _)
  refine ⟨(-j).toNat, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨k, hk⟩ := hodd
    exact ⟨(-k - 1).toNat, by omega⟩
  · rw [hs]
    exact hsz
  · simp only
    rw [hs]
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
