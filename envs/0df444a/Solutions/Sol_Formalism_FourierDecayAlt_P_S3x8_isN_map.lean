-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.isN_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:37.896681+00:00
-- url     : https://prove2.me/submissions/7c8be97e-e13e-41cc-8893-b73b25b3e1f6

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_upUni_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block22_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_map

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
theorem _root_.solution {B : Type} [CommRing B] (f : A →+* B) {x : Matrix (Idx r k) (Idx r k) A} (hx : IsN x) :
    IsN (x.map f) := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [block11_map]; exact upUni_map f h11
  · rw [block33_map]; exact upUni_map f h33
  · rw [block22_map, h22]; simp
  · rw [block21_map, h21]; ext; simp
  · rw [block31_map, h31]; ext; simp
  · rw [block32_map, h32]; ext; simp
end Formalism.FourierDecayAlt.P.S3x8
