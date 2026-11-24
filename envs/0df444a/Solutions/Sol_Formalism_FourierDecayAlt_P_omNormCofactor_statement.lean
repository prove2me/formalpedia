-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.omNormCofactor_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:26:21.316804+00:00
-- url     : https://prove2.me/submissions/2c97f984-b802-4009-a80b-f2035b959e46

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmegaNormCofactorOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_gram_cofactor_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_omega_norm_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.OmNormCofactor := by
  intro V _ _ B r f x' x ω z T T' hH hT hG hxx hxω hxz hωz hzz hcof
  have hv := gram_cofactor_identity V B r f x' T' hG
  rw [hcof] at hv
  exact omega_norm_identity V B x ω z T T' _ _ hH hT hxx hxω hxz hωz hzz hv
end Formalism.FourierDecayAlt.P
