-- Prove2me | solution 1 for Formalism.ExtensionFiltration.combinedAverageDegreeBound_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:48.127802+00:00
-- url     : https://prove2.me/submissions/cd1d74c8-fb61-44cd-afd5-21852790f04c

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CombinedAverageDegreeBound
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CombinedAverageDegreeBoundOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ExtensionFiltration
namespace Formalism.ExtensionFiltration
theorem _root_.solution (h1 : MeanHeights) (h2 : SumComponents) : CombinedAverageDegreeBound := by
  intro ι _ _ T D A cs X cc z ρ R1 R2 Bn δ' h sl δ dc degc LL0 U b Ca Cb PPf e1 e2 muU hD hT hA hcs hX hcc
    hz0 hz1 hρ0 hρ1 hR1 hR2 hBn hδ' hδ hdc hhc hsl hmean hdeg hTX hTcc hb hmu
  have hm := h1 ι h sl cs cc ρ X hρ0 hρ1.le hX hhc hsl hmean
  have hs := h2 ι T D A cs X cc z ρ R1 R2 Bn δ' h δ dc degc hD hT hA hcs hX hcc hz0 hz1 hρ0 hρ1 hR1 hR2
    hBn hδ' hδ hdc (fun c => by linarith [hhc c]) hdeg hm
  nlinarith
end Formalism.ExtensionFiltration
