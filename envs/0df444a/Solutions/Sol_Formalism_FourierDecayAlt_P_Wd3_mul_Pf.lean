-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd3.mul_Pf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:43.996841+00:00
-- url     : https://prove2.me/submissions/3088cf5b-9e6e-4f73-80a5-03c1b982ee5c

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
theorem _root_.solution {B : Type} [Ring B] (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (j s : Fin 2)
    (x : Fin 2 × Fin 2) : (X * Pf B) x (j, s) = X x (s, j) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Pf, ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
end Formalism.FourierDecayAlt.P.Wd3
