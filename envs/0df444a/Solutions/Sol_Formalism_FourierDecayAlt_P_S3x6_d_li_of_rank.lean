-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_li_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:03.924171+00:00
-- url     : https://prove2.me/submissions/3b40f369-65c2-4d24-ad9d-0239b1e98f01

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Matrix Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a) :
    LinearIndependent K (fun (i : Fin a) (k : Fin n) => X k i) := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  have h1 := Matrix.range_mulVecLin X
  unfold Matrix.rank at hX
  rw [h1] at hX
  exact hX.symm
end Formalism.FourierDecayAlt.P.S3x6
