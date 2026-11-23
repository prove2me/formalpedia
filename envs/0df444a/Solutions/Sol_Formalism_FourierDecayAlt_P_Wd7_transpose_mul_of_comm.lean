-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.transpose_mul_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:14.94504+00:00
-- url     : https://prove2.me/submissions/00e6bb95-8d9b-4427-ad56-e5a10e7aa864

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution {B : Type} [Ring B] (M N : M2 B)
    (h : ∀ i j k l, Commute (M i j) (N k l)) : (M * N)ᵀ = Nᵀ * Mᵀ := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun m _ => (h j m m i).eq
end Formalism.FourierDecayAlt.P.Wd7
