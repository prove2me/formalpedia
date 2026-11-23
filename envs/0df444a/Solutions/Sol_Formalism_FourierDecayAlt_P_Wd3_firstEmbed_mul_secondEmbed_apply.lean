-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd3.firstEmbed_mul_secondEmbed_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:36.314591+00:00
-- url     : https://prove2.me/submissions/4f1f86f7-74d5-46d2-bc80-417e76347e8e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd3
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd3
theorem _root_.solution {B : Type} [Ring B] (M N : M2 B) (i r j s : Fin 2) :
    (E1 M * E2 N) (i, r) (j, s) = M i j * N r s := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
end Formalism.FourierDecayAlt.P.Wd3
