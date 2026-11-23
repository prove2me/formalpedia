-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.isN_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:12.253972+00:00
-- url     : https://prove2.me/submissions/d7599bad-26aa-4fa8-ac87-aa63c3cb5e0a

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block11_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block12_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block13_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block21_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block22_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block23_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block31_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block32_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block33_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block11_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block12_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block13_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block21_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block22_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block23_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block31_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block32_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block33_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block11_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block12_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block13_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block21_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block22_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block23_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block31_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block32_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block33_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block11_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block12_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block13_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block21_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block22_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block23_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block31_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block32_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block33_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_midEmb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_midEmb_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block11_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block12_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block13_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block21_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block22_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block23_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block31_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block32_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block33_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block11_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block12_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block13_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block21_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block22_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block23_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block31_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block32_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block33_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block11_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block12_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block13_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block21_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block22_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block23_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block31_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block32_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block33_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block11_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block12_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block13_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block21_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block22_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block23_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block31_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block32_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block33_levi_embedding_mul

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x3
theorem _root_.solution {a b : Matrix (Fin k) (Fin k) A} (hab : a * b = 1)
    {n : Matrix (Idx r k) (Idx r k) A} (hn : IsN n) : IsN (hEmb r a * n * hEmb r b) := by
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  refine ⟨by simpa using h11, by simpa using h33, ?_, ?_, ?_, ?_⟩
  · simp [h22, ← midEmb_mul, hab, midEmb_one]
  · simp [h21]
  · simp [h31]
  · simp [h32]
end Formalism.FourierDecayAlt.P.S3x3
