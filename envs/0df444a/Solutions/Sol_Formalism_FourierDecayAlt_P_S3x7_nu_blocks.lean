-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.nu_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:19.883913+00:00
-- url     : https://prove2.me/submissions/d9afd280-389a-46fe-9766-a190c0c6c2fa

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_block11_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_block21_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_block22_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_block31_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_block32_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_block33_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_levi_embedding_block11
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_levi_embedding_block12
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_levi_embedding_block13
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_levi_embedding_block21
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_levi_embedding_block22
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_levi_embedding_block23
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_levi_embedding_block31
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_levi_embedding_block32
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_levi_embedding_block33
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_midEmb_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {x : Matrix (Idx r k) (Idx r k) A} (hx : IsNU x) :
    IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0 ∧ IsUnit (b22 x).det := by
  obtain ⟨n, _, ⟨h11, h33, h22, h21, h31, h32⟩, ⟨h, hh, rfl⟩, rfl⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [block11_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31]; simpa using h11
  · rw [block33_mul, levi_embedding_block13, levi_embedding_block23, levi_embedding_block33]; simpa using h33
  · rw [block21_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h21]; simp
  · rw [block31_mul, levi_embedding_block11, levi_embedding_block21, levi_embedding_block31, h31]; simp
  · rw [block32_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h32]; simp
  · rw [block22_mul, levi_embedding_block12, levi_embedding_block22, levi_embedding_block32, h22]
    simp [midEmb_det, isUpUni_det A hh]
end Formalism.FourierDecayAlt.P.S3x7
