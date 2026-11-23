-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.bt_of_isNU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:13.156004+00:00
-- url     : https://prove2.me/submissions/e3908c2f-2735-4fef-9147-73b84ec42eea

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_uni_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_bt_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_bt_of_isN

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
theorem _root_.solution {x : Matrix (Idx r k) (Idx r k) A} (hx : IsNU x) : BT x := by
  obtain ⟨n, _, hn, ⟨u, hu, rfl⟩, rfl⟩ := hx
  refine bt_mul (bt_of_isN hn) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : b11 (hEmb r u) = 1 := by ext a b; simp [b11, hEmb]
    rw [this]; exact isUpUni_one A
  · have : b33 (hEmb r u) = 1 := by ext a b; simp [b33, hEmb]
    rw [this]; exact isUpUni_one A
  · ext a b; simp [b21, hEmb]
  · ext a b; simp [b31, hEmb]
  · ext a b; simp [b32, hEmb]
  · have : b22 (hEmb r u) = midEmb u := by ext a b; simp [b22, hEmb]
    rw [this]; simpa [midEmb] using uni_unit hu
end Formalism.FourierDecayAlt.P.S3x8
