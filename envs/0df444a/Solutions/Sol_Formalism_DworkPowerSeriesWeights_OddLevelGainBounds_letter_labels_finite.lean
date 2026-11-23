-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.letter_labels_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:38.395735+00:00
-- url     : https://prove2.me/submissions/a39b72c8-5ebc-4189-9ce1-d96b4bdd5d1b

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_CapLeOddShiftBound

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
theorem _root_.solution : LabFinite7 := by
  intro l d _ hl TT nu1 size s
  set M : ℕ := Finset.univ.sup nu1 + Dl d TT nu1 size s with hM
  apply ((Set.finite_univ (α := ZMod d)).prod (Set.finite_Icc (-(M : ℤ)) (M : ℤ))).subset
  rintro ⟨s0, j⟩ ⟨_, _, _, hp, hn⟩
  simp only at hp hn
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · show -(M : ℤ) ≤ j
    by_cases hj : j < 0
    · have h1 := hn hj
      have h2 : (-j).toNat < l ^ (-j).toNat := Nat.lt_pow_self (by omega)
      omega
    · omega
  · show j ≤ (M : ℤ)
    by_cases hj : 0 < j
    · have h1 := hp hj
      have h2 : j.toNat < l ^ j.toNat := Nat.lt_pow_self (by omega)
      have h3 : nu1 s0 ≤ Finset.univ.sup nu1 := Finset.le_sup (f := nu1) (Finset.mem_univ s0)
      omega
    · omega
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
