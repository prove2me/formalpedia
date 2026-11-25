-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedMeanLemmas.weighted_mean_lemma_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:00:50.142525+00:00
-- url     : https://prove2.me/submissions/9dced189-82c7-4e43-8a89-a4b0805f3f6c

import Definitions.Def_Formalism_SizeWindowBrackets_RealSlopeBoundsSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_mono__ee8853d08dcc
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_const__aac77132a99d
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_add__e2817b45bf86
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedMeanLemmas_wmean_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedMeanLemmas
open Finset
namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas
theorem _root_.solution (ι : Type*) [Fintype ι] [Nonempty ι] : LemmaUge ι := by
  intro d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr hS2
  obtain ⟨hmax, hmu⟩ := hS2
  have h1 : wmean d (fun u => muM u - h u) + Sg0 - wmean d (fun u => dr u + BE u)
      ≤ sF d muN h := by
    have e : wmean d (fun u => (muM u - h u + Sg0) - (dr u + BE u))
        = wmean d (fun u => muM u - h u) + Sg0 - wmean d (fun u => dr u + BE u) := by
      rw [wmean_sub d (fun u => muM u - h u + Sg0) (fun u => dr u + BE u),
        wmean_add' d (fun u => muM u - h u) (fun _ => Sg0), wmean_const' hd]
    rw [← e]
    unfold sF
    exact wmean_mono' hd fun u => by linarith [hmu u]
  have h2 : umax (fun u => muMaxN u - h u) ≤ umax (fun u => muMaxM u - h u) + Sg0 := by
    unfold umax
    apply Finset.sup'_le
    intro u _
    have : muMaxM u - h u ≤ Finset.univ.sup' Finset.univ_nonempty (fun u => muMaxM u - h u) :=
      Finset.le_sup' (fun u => muMaxM u - h u) (Finset.mem_univ u)
    linarith [hmax u, hdr u]
  unfold uF rhsU
  linarith
end Formalism.LFunctionChainParameters.WeightedMeanLemmas
