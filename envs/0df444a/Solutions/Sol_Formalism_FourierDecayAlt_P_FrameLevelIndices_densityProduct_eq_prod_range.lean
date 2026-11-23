-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameLevelIndices.densityProduct_eq_prod_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:10.882797+00:00
-- url     : https://prove2.me/submissions/15585752-7215-472a-9569-f30c9160c9d4

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block11_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block11_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block11_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block11_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block12_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block12_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block12_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block12_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block13_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block13_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block13_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block13_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block21_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block21_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block21_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block21_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block22_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block22_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block22_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block22_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block23_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block23_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block23_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block23_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block31_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block31_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block31_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block31_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block32_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block32_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block32_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block32_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block33_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block33_levi_embedding_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block33_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_block33_mul_levi_embedding
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x2.coe_phi
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block11_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block11_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block11_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block11_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block12_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block12_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block12_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block12_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block13_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block13_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block13_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block13_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block21_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block21_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block21_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block21_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block22_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block22_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block22_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block22_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block23_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block23_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block23_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block23_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block31_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block31_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block31_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block31_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block32_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block32_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block32_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block32_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block33_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block33_levi_embedding_mul
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block33_map
attribute [local simp] Formalism.FourierDecayAlt.P.S3x3.block33_mul_levi_embedding
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll



set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameLevelIndices
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_one)
open Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.FrameLevelIndices
theorem _root_.solution (q a m : ℕ) :
    densP 1 q ((a : ℤ) + 1) ((a + m : ℕ) : ℤ) = ∏ x ∈ range m, fac q (a + x) := by
  unfold densP
  refine Finset.prod_nbij' (fun i => (i - a - 1).toNat) (fun x => (a : ℤ) + 1 + x) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro x hx
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    omega
  · intro x hx
    show ((a : ℤ) + 1 + x - a - 1).toNat = x
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    obtain ⟨x, rfl⟩ : ∃ x : ℕ, i = (a : ℤ) + 1 + x := ⟨(i - a - 1).toNat, by omega⟩
    have e1 : ((a : ℤ) + 1 + x - a - 1).toNat = x := by omega
    have e2 : (a : ℤ) + 1 + x = ((a + x + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2, fac]
    simp only [Int.cast_one, one_pow, one_mul, _root_.zpow_neg, zpow_natCast]
end Formalism.FourierDecayAlt.P.FrameLevelIndices
