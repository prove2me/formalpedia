-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.transpose_mul_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:46.764812+00:00
-- url     : https://prove2.me/submissions/1a8b7bbd-07b9-46f3-901b-54ac2c27036f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {B : Type} [Ring B]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution {M N : M2 B} (h : ∀ i j, EC (M i j) N) :
    (M * N)ᵀ = Nᵀ * Mᵀ := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (h j k k i).eq
end Formalism.FourierDecayAlt.P.Wd6
