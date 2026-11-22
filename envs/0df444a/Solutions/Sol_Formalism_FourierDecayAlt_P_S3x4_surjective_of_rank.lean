-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.surjective_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:34.983903+00:00
-- url     : https://prove2.me/submissions/d4e8fde8-34e9-4bc7-8767-641c48111401

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
variable {K : Type} [Field K]
namespace Formalism.FourierDecayAlt.P.S3x4
theorem _root_.solution {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a) :
    Function.Surjective (Matrix.toLin' Xᵀ) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have h := Matrix.rank_transpose X
  rw [Matrix.rank, ← Matrix.toLin'_apply', hX] at h
  rw [Module.finrank_fin_fun, h]
end Formalism.FourierDecayAlt.P.S3x4
