-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.residue_partial_fractions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:13.841026+00:00
-- url     : https://prove2.me/submissions/1055bcce-b689-4671-bddf-abe6fc868c62

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : ResidueStep := by
  intro B _ _ Z γ Ya Y h1 h2 h3
  have e1 : Y - γ ≠ 0 := sub_ne_zero.mpr h1
  have e2 : Ya - γ ≠ 0 := sub_ne_zero.mpr h2
  have e3 : Y - Ya ≠ 0 := sub_ne_zero.mpr h3
  constructor
  · simp only [← sub_smul, smul_smul]
    congr 1
    first | (field_simp; ring) | field_simp | ring
  · simp only [← sub_smul, ← add_smul, smul_smul]
    congr 1
    first | (field_simp; ring) | field_simp | ring
end Formalism.FourierDecayAlt.P
