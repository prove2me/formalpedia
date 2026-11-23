-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:23.230912+00:00
-- url     : https://prove2.me/submissions/a0e9e744-8282-4bda-b15f-0d8a849403b2

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_hJ_apply

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
theorem _root_.solution {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hi : Inv σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (hJh : fconj q J = J) : Herm (hJ σ J) := by
  intro u v
  rw [hJ_apply, hJ_apply, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : σ (J j i) = J i j := by
    have := congrFun (congrFun hJh i) j
    simpa [fconj, hσ] using this
  rw [map_mul, map_mul, hi.invol, h1]
  ring
end Formalism.FourierDecayAlt.P.S3x6
