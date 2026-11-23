-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.bt_of_isN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:20.031781+00:00
-- url     : https://prove2.me/submissions/fd998cd2-f4b9-4866-a33b-6e79c8ab1276

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {x : Matrix (Idx r k) (Idx r k) A} (hx : IsN x) : BT x := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hx
  exact ⟨h11, h33, h21, h31, h32, by rw [h22]; simp⟩
end Formalism.FourierDecayAlt.P.S3x8
