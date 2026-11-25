-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:20:01.376554+00:00
-- url     : https://prove2.me/submissions/e86eea59-3ce8-4624-aa57-f8f99959edf1

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_upUni_of_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_ext9
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block12_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block12_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block13_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block13_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block22_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block22_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block23_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block23_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_uni_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block12_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block13_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block22_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block23_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_of_blocks

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
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {r k : ℕ}
variable [IsDomain o] [IsDiscreteValuationRing o] [IsFractionRing o k0]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {n : Matrix (Idx r k) (Idx r k) k0} (hn : IsN n) (i11 : Integral o (b11 n))
    (i12 : Integral o (b12 n)) (i23 : Integral o (b23 n)) (i33 : Integral o (b33 n)) :
    ∃ (m : Matrix (Idx r k) (Idx r k) o) (S : Matrix (Fin r) (Fin r) k0),
      IsN m ∧ n = cen S * m.map (algebraMap o k0) := by
  have hinj : Function.Injective (algebraMap o k0) := IsFractionRing.injective o k0
  obtain ⟨h11, h33, h22, h21, h31, h32⟩ := hn
  obtain ⟨u1, hu1⟩ := i11
  obtain ⟨a, ha⟩ := i12
  obtain ⟨a', ha'⟩ := i23
  obtain ⟨u2, hu2⟩ := i33
  refine ⟨mk u1 a 0 1 a' u2, b13 n * (b33 n)⁻¹, ⟨?_, ?_, block22_of_blocks .., block21_of_blocks .., block31_of_blocks .., block32_of_blocks ..⟩, ?_⟩
  · rw [block11_of_blocks]; exact upUni_of_map _ hinj (hu1 ▸ h11)
  · rw [block33_of_blocks]; exact upUni_of_map _ hinj (hu2 ▸ h33)
  · have hz : (b33 n)⁻¹ * b33 n = 1 := Matrix.nonsing_inv_mul _ (uni_unit h33)
    apply ext9 <;>
      simp only [cen, block11_mul, block12_mul, block13_mul, block21_mul, block22_mul, block23_mul, block31_mul, block32_mul, block33_mul,
        block11_map, block12_map, block13_map, block21_map, block22_map, block23_map, block31_map, block32_map, block33_map,
        block11_of_blocks, block12_of_blocks, block13_of_blocks, block21_of_blocks, block22_of_blocks, block23_of_blocks, block31_of_blocks, block32_of_blocks, block33_of_blocks, hu1, ha, ha', hu2,
        h22, h21, h31, h32] <;>
      simp [Matrix.mul_assoc, hz]
end Formalism.FourierDecayAlt.P.S3x8
