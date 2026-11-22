-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.hJ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:29.184858+00:00
-- url     : https://prove2.me/submissions/241509ed-595b-4749-a7a4-7ffecea75f20

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
theorem _root_.solution {n : ℕ} (J : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    hJ σ J u v = ∑ i, ∑ j, σ (u i) * J i j * v j := by
  unfold hJ
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply, smul_eq_mul]
  ring
end Formalism.FourierDecayAlt.P.S3x6
