-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.isN_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:38.371801+00:00
-- url     : https://prove2.me/submissions/b902aafb-2873-4853-8e40-419d1632a7ea

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
theorem _root_.solution (x : Matrix (Idx r k) (Idx r k) A) : IsN x ↔ Par (fun h => h = 1) x := by
  constructor
  · rintro ⟨h11, h33, h22, h21, h31, h32⟩
    exact ⟨h11, h33, h21, h31, h32, 1, rfl, by rw [h22, midEmb_one]⟩
  · rintro ⟨h11, h33, h21, h31, h32, h, rfl, h22⟩
    exact ⟨h11, h33, by rw [h22, midEmb_one], h21, h31, h32⟩
end Formalism.FourierDecayAlt.P.S3x1
