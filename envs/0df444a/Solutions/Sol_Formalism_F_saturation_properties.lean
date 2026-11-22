-- Prove2me | solution 1 for Formalism.F.saturation_properties
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:45.144735+00:00
-- url     : https://prove2.me/submissions/edfb3841-18c5-4b7a-9dab-70bb651dd91b

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Theorems.Thm_Formalism_F_rank_eq_finrank_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution : SaturProps := by
  intro E _ _ _ L N hL hNL
  haveI := hL
  have hSL : satur L N ≤ L := inf_le_left
  have hNS : N ≤ satur L N := fun x hx => ⟨hNL hx, Submodule.subset_span hx⟩
  have hspan : span ℝ (satur L N : Set E) = span ℝ (N : Set E) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      exact fun x hx => hx.2
    · exact Submodule.span_mono hNS
  refine ⟨⟨hSL, fun x hx hxs => ⟨hx, ?_⟩⟩, hNS, ?_⟩
  · rw [hspan] at hxs
    exact hxs
  · haveI : DiscreteTopology (satur L N) := DiscreteTopology.of_subset (s := (L : Set E)) hL hSL
    haveI : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hNL
    rw [rank_eq_finrank_span, rank_eq_finrank_span, hspan]
end Formalism.F
