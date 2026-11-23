-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.blockMinorWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:31.921638+00:00
-- url     : https://prove2.me/submissions/fc7f0bb2-46c6-4689-8339-9fe733a9e0b4

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open scoped ComplexOrder ComplexConjugate
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
theorem _root_.solution {E : Type} [Field E] [NumberField E] {r : ℕ} (γ : Pts E r) :
    0 < Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ := by
  unfold Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight
  exact Finset.prod_pos fun a _ => Finset.prod_pos fun w _ => by positivity
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E
