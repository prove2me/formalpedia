-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.forcing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:10:08.067195+00:00
-- url     : https://prove2.me/submissions/40ea4afb-7898-468a-a7ee-9bfdd2244ece

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_centreForcing
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block13_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block13_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_bt_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_bt_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_bt_rinv
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_bt_of_isN
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_bt_of_isNU
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_isN_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block12_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block13_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block22_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block23_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_cen
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_decomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_halfForce
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_invOm

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
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution : Forcing := by
  intro o _ _ _ k0 _ _ _ ϖ hϖ r k j j' n n' hj hj' hn hn' e
  obtain ⟨⟨hjd, hjNU⟩, X, hX, hc⟩ := hj
  have bj := bt_of_isNU hjNU
  have bj' := bt_of_isNU hj'.2
  have j1 : j⁻¹ * j = 1 := Matrix.nonsing_inv_mul j hjd
  have j1' : j' * j'⁻¹ = 1 := Matrix.mul_nonsing_inv j' hj'.1
  obtain ⟨i33, i11', i23, i12', X', hX', hc'⟩ := halfForce hϖ bj hX hc bj' hn hn' e
  obtain ⟨bi, Y, hY, hcY⟩ := invOm hϖ hjd bj hX hc
  have bi' : BT (j'⁻¹.map (IsLocalRing.residue o)) :=
    bt_rinv bj' (by rw [← Matrix.map_mul, j1']; simp)
  have J1 : j⁻¹.map (algebraMap o k0) * j.map (algebraMap o k0) = 1 := by
    rw [← Matrix.map_mul, j1]; simp
  have J1' : j'.map (algebraMap o k0) * j'⁻¹.map (algebraMap o k0) = 1 := by
    rw [← Matrix.map_mul, j1']; simp
  have e' : n' * j'⁻¹.map (algebraMap o k0) = j⁻¹.map (algebraMap o k0) * n := by
    calc n' * j'⁻¹.map (algebraMap o k0)
        = j⁻¹.map (algebraMap o k0) * (j.map (algebraMap o k0) * n') * j'⁻¹.map (algebraMap o k0) := by
          simp only [← mul_assoc, J1, one_mul]
      _ = j⁻¹.map (algebraMap o k0) * (n * j'.map (algebraMap o k0)) * j'⁻¹.map (algebraMap o k0) := by
          rw [e]
      _ = j⁻¹.map (algebraMap o k0) * n := by simp only [mul_assoc, J1', mul_one]
  obtain ⟨i33', i11, i23', i12, -⟩ := halfForce hϖ bi hY hcY bi' hn' hn e'
  obtain ⟨m, S, hm, hnS⟩ := decomp hn i11 i12 i23 i33
  obtain ⟨m', S', hm', hnS'⟩ := decomp hn' i11' i12' i23' i33'
  have m1 : m' * m'⁻¹ = 1 := Matrix.mul_nonsing_inv m' (bt_det (bt_of_isN hm'))
  have M1 : m'.map (algebraMap o k0) * m'⁻¹.map (algebraMap o k0) = 1 := by
    rw [← Matrix.map_mul, m1]; simp
  have bj'' : BT ((m * j' * m'⁻¹).map (IsLocalRing.residue o)) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    exact bt_mul (bt_mul (bt_of_isN (isN_map _ hm)) bj')
      (bt_rinv (bt_of_isN (isN_map _ hm')) (by rw [← Matrix.map_mul, m1]; simp))
  have e'' : cen S * (m * j' * m'⁻¹).map (algebraMap o k0) = j.map (algebraMap o k0) * cen S' := by
    rw [Matrix.map_mul, Matrix.map_mul]
    calc cen S * (m.map (algebraMap o k0) * j'.map (algebraMap o k0) * m'⁻¹.map (algebraMap o k0))
        = (cen S * m.map (algebraMap o k0)) * j'.map (algebraMap o k0) * m'⁻¹.map (algebraMap o k0) := by
          simp only [mul_assoc]
      _ = j.map (algebraMap o k0) * (cen S' * m'.map (algebraMap o k0)) * m'⁻¹.map (algebraMap o k0) := by
          rw [← hnS, e, ← hnS']
      _ = j.map (algebraMap o k0) * cen S' := by simp only [mul_assoc, M1, mul_one]
  generalize m * j' * m'⁻¹ = j'' at bj'' e''
  have f31 := congrArg b31 e''
  have f11 := congrArg b11 e''
  have f33 := congrArg b33 e''
  have f13 := congrArg b13 e''
  simp only [cen, block11_mul, block13_mul, block31_mul, block33_mul, block11_of_blocks, block12_of_blocks, block13_of_blocks, block21_of_blocks, block22_of_blocks, block23_of_blocks,
    block31_of_blocks, block32_of_blocks, block33_of_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul, block11_map, block13_map, block31_map, block33_map] at f31 f11 f33 f13
  rw [f31] at f11
  rw [hX] at f11 f33
  have E1 : (b11 j'').map (algebraMap o k0) =
      (b11 j).map (algebraMap o k0) - S * (ϖ • X).map (algebraMap o k0) := eq_sub_of_add_eq f11
  have E2 : (b33 j'').map (algebraMap o k0) =
      (b33 j).map (algebraMap o k0) + (ϖ • X).map (algebraMap o k0) * S' := by rw [f33, add_comm]
  have E3 : (b13 j'').map (algebraMap o k0) = (b13 j).map (algebraMap o k0) -
      S * (b33 j).map (algebraMap o k0) +
        ((b11 j).map (algebraMap o k0) - S * (ϖ • X).map (algebraMap o k0)) * S' := by
    rw [eq_sub_of_add_eq f13, E2]; noncomm_ring
  obtain ⟨iS, iS'⟩ := centreForcing o k0 ϖ hϖ r (b11 j) (b33 j) (b13 j) X (b11 j'') (b33 j'') (b13 j'')
    S S' bj.1 bj.2.1 hc bj''.1 bj''.2.1 E1 E2 E3
  refine ⟨?_, ?_, hj', X', hX', hc'⟩
  · rw [hnS]; exact int_mul (int_cen iS) (int_map m)
  · rw [hnS']; exact int_mul (int_cen iS') (int_map m')
end Formalism.FourierDecayAlt.P.S3x8
