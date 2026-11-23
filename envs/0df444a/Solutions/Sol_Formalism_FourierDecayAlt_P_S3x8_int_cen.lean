-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.int_cen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:22.088886+00:00
-- url     : https://prove2.me/submissions/f78c92f6-e6a0-41f8-a1a4-58cb3c3a150a

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_ext9
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block11_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block12_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block13_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block21_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block22_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block23_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block31_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block32_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_block33_map
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
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {S : Matrix (Fin r) (Fin r) k0} (h : Integral o S) :
    Integral o (cen S : Matrix (Idx r k) (Idx r k) k0) := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨cen s, ?_⟩
  apply ext9 <;>
    simp [cen, block11_map, block12_map, block13_map, block21_map, block22_map, block23_map, block31_map, block32_map, block33_map,
      block11_of_blocks, block12_of_blocks, block13_of_blocks, block21_of_blocks, block22_of_blocks, block23_of_blocks, block31_of_blocks, block32_of_blocks, block33_of_blocks]
end Formalism.FourierDecayAlt.P.S3x8
