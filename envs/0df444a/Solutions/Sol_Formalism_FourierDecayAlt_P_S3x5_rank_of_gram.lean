-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.rank_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:22.364654+00:00
-- url     : https://prove2.me/submissions/bdfc6e6c-4977-4bae-bc64-5d573e863a5f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {ν α : Type} [Fintype ν] [DecidableEq ν] [Fintype α] [DecidableEq α]
    (J : Matrix ν ν K) (T : Matrix α α K) (hdT : IsUnit T.det) (X : Matrix ν α K)
    (h : Xᴴ * J * X = T) : X.rank = Fintype.card α := by
  apply le_antisymm (rank_le_card_width X)
  have h1 := rank_mul_le_right (Xᴴ * J) X
  rw [h, rank_of_isUnit T ((isUnit_iff_isUnit_det T).2 hdT)] at h1
  exact h1
end Formalism.FourierDecayAlt.P.S3x5
