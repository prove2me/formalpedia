-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd3.Pf_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:54.962199+00:00
-- url     : https://prove2.me/submissions/5d07409b-81e3-4474-9e67-1eda9cb83332

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
theorem _root_.solution {B : Type} [Ring B] (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i r : Fin 2)
    (y : Fin 2 × Fin 2) : (Pf B * X) (i, r) y = X (r, i) y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Pf, ite_and, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
end Formalism.FourierDecayAlt.P.Wd3
