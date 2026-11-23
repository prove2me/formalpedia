-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.pow_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:13.06429+00:00
-- url     : https://prove2.me/submissions/783ee7cf-95a5-49f6-ab86-3a13cf494882

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
variable {Cl Nu : Type}
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
theorem _root_.solution {P : Type} [Fintype P] (Om : Finset P) (a : ℝ) :
    a ^ Om.card = ∏ p, if p ∈ Om then a else 1 := by
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
