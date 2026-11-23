-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.subgroupSet_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:52.514927+00:00
-- url     : https://prove2.me/submissions/f748e0c0-2864-47eb-a6f8-c27fef3c0174

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
theorem _root_.solution {Q Q' : Matrix (Idx r k) (Idx r k) A → Prop} (h : ∀ x, Q x ↔ Q' x)
    (hQ : IsSubgroupSet Q') : IsSubgroupSet Q := by
  obtain ⟨B, hB⟩ := hQ
  exact ⟨B, fun x => (h x).trans (hB x)⟩
end Formalism.FourierDecayAlt.P.S3x1
