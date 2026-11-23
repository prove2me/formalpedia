-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.emb_par
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:52.241791+00:00
-- url     : https://prove2.me/submissions/7d1c9589-909f-4434-b33b-80d606bd968a

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
variable {P : Matrix (Fin k) (Fin k) A → Prop}
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution (hP : GP P) {x : Matrix (Idx r k) (Idx r k) A} (hx : Emb P x) : Par P x := by
  obtain ⟨h, hh, rfl⟩ := hx
  exact ⟨by rw [levi_embedding_block11]; exact isUpUni_one A, by rw [levi_embedding_block33]; exact isUpUni_one A, levi_embedding_block21 h,
    levi_embedding_block31 h, levi_embedding_block32 h, h, hh, levi_embedding_block22 h⟩
end Formalism.FourierDecayAlt.P.S3x1
