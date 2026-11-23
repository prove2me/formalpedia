-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.finrank_ker_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:56.837616+00:00
-- url     : https://prove2.me/submissions/94749dd2-4290-48a9-8d2c-e3396108f85a

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_surjective_of_rank

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
    finrank K (LinearMap.ker (Matrix.toLin' Xᵀ)) = n - a := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' Xᵀ)
  rw [Module.finrank_fin_fun, LinearMap.range_eq_top.mpr (surjective_of_rank X hX), finrank_top,
    Module.finrank_fin_fun] at h
  omega
end Formalism.FourierDecayAlt.P.S3x4
