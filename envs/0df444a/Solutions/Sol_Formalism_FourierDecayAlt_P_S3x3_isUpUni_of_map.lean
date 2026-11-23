-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.isUpUni_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:25.758443+00:00
-- url     : https://prove2.me/submissions/6e855e09-f12a-450c-b2a2-af9af1f5baa8

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
theorem _root_.solution {B : Type} [CommRing B] (f : A →+* B) (hf : Function.Injective f) {n : ℕ}
    {x : Matrix (Fin n) (Fin n) A} (hx : IsUpUni (x.map f)) : IsUpUni x :=
  ⟨fun i j hij => hf (by simpa using hx.1 hij), fun a => hf (by simpa using hx.2 a)⟩
end Formalism.FourierDecayAlt.P.S3x3
