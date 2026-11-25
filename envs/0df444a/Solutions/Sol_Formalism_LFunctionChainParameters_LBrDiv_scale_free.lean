-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.scale_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:29:31.278454+00:00
-- url     : https://prove2.me/submissions/daf2132c-3af6-4976-a49a-212152e0460f

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBrDiv
theorem _root_.solution : ScaleFree := by
  intro U0 W _ Top _ m f D C c logOm hd hne
  have hs : ∀ u0, (shiftRows D c).s u0 = D.s u0 + c u0 := by
    intro u0
    have := hne u0
    have hpos : 0 < ∑ u, D.d u0 u := Finset.sum_pos (fun u _ => hd u0 u) Finset.univ_nonempty
    show wmean (D.d u0) (fun u => D.muN u0 u - (D.h u0 u - c u0))
      = wmean (D.d u0) (fun u => D.muN u0 u - D.h u0 u) + c u0
    unfold wmean
    rw [eq_comm, div_add' _ _ _ hpos.ne']
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  have e1 : ∀ u0 (u : W u0), (D.muCC u0 + c u0) + (D.h u0 u - c u0) - D.Fo u0
      = D.muCC u0 + D.h u0 u - D.Fo u0 := fun u0 u => by ring
  refine ⟨?_, ?_, ?_, ?_, hs⟩
  · constructor
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u]
      exact this
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u] at this
      exact this
  · constructor
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u]
      exact this
    · intro h u0 u
      have := h u0 u
      rw [← e1 u0 u] at this
      exact this
  · have e2 : ∀ u0 (u u' : W u0),
        ((D.h u0 u - c u0) + ∑ t, D.aT t * Real.log (D.T u0 u))
          - ((D.h u0 u' - c u0) + ∑ t, D.aT t * Real.log (D.T u0 u'))
        = (D.h u0 u + ∑ t, D.aT t * Real.log (D.T u0 u))
          - (D.h u0 u' + ∑ t, D.aT t * Real.log (D.T u0 u')) := fun u0 u u' => by ring
    constructor
    · intro h u0 u u'
      have := h u0 u u'
      rw [← e2 u0 u u']
      exact this
    · intro h u0 u u'
      have := h u0 u u'
      rw [← e2 u0 u u'] at this
      exact this
  · have e3 : ∀ u0, (shiftRows D c).s u0 - (D.muMinCC u0 + c u0) = D.s u0 - D.muMinCC u0 := by
      intro u0
      rw [hs u0]
      ring
    constructor
    · intro h u0
      have := h u0
      rw [← e3 u0]
      exact this
    · intro h u0
      have := h u0
      rw [← e3 u0] at this
      exact this
end Formalism.LFunctionChainParameters.LBrDiv
