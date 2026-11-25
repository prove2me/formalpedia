-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.poisson_joint_first_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:54:24.454006+00:00
-- url     : https://prove2.me/submissions/37ca9c7d-c36b-4a9f-ad86-4afa81cb752d

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.PoissonJointTA := by
  intro hF hJ E _ _ D H _ _ W _ Φ tr i V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hinj hmem hd0 hdual hW
  intro w Hd kap hHd hk t0 T hT B hB
  obtain ⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩ := hW w Hd kap hHd hk
  have key := hJ hF V ι π hπ Λ E emb dmap (D.La i 1) (D.Lv i) φ Cφ (tr w Hd kap)
    hinj hmem hd0 hdual hc hb hnn hhat t0 B hB T (fun t ht => (hT t ht).2)
  refine Eq.trans_le ?_ key
  exact Finset.sum_congr rfl fun t ht => hdiag t (hT t ht).1
end Formalism.FourierDecayAlt.P
