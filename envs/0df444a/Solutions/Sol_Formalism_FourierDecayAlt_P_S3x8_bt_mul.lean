-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.bt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:26:08.864794+00:00
-- url     : https://prove2.me/submissions/6cd3a886-7f2c-42c5-a2e2-a9536fad3744

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block22_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_mul

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
theorem _root_.solution {x y : Matrix (Idx r k) (Idx r k) A} (hx : BT x) (hy : BT y) : BT (x * y) := by
  obtain ⟨h11, h33, h21, h31, h32, h22⟩ := hx
  obtain ⟨g11, g33, g21, g31, g32, g22⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [block11_mul, g21, g31]; simpa using isUpUni_mul A h11 g11
  · rw [block33_mul, h31, h32]; simpa using isUpUni_mul A h33 g33
  · rw [block21_mul, h21, g21, g31]; simp
  · rw [block31_mul, h31, h32, g31]; simp
  · rw [block32_mul, h31, h32, g32]; simp
  · rw [block22_mul, h21, g32]; simpa using h22.mul g22
end Formalism.FourierDecayAlt.P.S3x8
