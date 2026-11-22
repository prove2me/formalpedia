-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.rank_eq_iff_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:08:35.284549+00:00
-- url     : https://prove2.me/submissions/1a82335d-5420-4497-a7f7-37396e6ce98a

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
theorem _root_.solution {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) :
    X.rank = a ↔ Function.Injective (Matrix.toLin' X) := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' X)
  rw [Module.finrank_fin_fun] at h
  have h0 : X.rank = finrank K (LinearMap.range (Matrix.toLin' X)) := by
    rw [Matrix.rank, Matrix.toLin'_apply']
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero, h0]
  omega
end Formalism.FourierDecayAlt.P.S3x4
