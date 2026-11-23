-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.parMap_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:52.305468+00:00
-- url     : https://prove2.me/submissions/59902dba-8c3b-4665-af81-8c887aecb27f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_ext9
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_midEmb_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_block13_of_blocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]
variable {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution (P : Matrix (Fin k) (Fin k) A → Prop) : Function.Bijective (parMap (r := r) P) := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨f, hf⟩, ⟨h, hh⟩, b, c, e⟩ ⟨⟨a', ha'⟩, ⟨f', hf'⟩, ⟨h', hh'⟩, b', c', e'⟩ E
    have E' := congrArg Subtype.val E
    simp only [parMap] at E'
    have e11 := congrArg b11 E'
    have e12 := congrArg b12 E'
    have e13 := congrArg b13 E'
    have e22 := congrArg b22 E'
    have e23 := congrArg b23 E'
    have e33 := congrArg b33 E'
    rw [block11_of_blocks, block11_of_blocks] at e11
    rw [block12_of_blocks, block12_of_blocks] at e12
    rw [block13_of_blocks, block13_of_blocks] at e13
    rw [block22_of_blocks, block22_of_blocks] at e22
    rw [block23_of_blocks, block23_of_blocks] at e23
    rw [block33_of_blocks, block33_of_blocks] at e33
    have e22' := midEmb_inj e22
    subst e11 e12 e13 e22' e23 e33
    rfl
  · rintro ⟨x, h11, h33, h21, h31, h32, h, hh, h22⟩
    refine ⟨⟨⟨b11 x, h11⟩, ⟨b33 x, h33⟩, ⟨h, hh⟩, b12 x, b13 x, b23 x⟩, Subtype.ext ?_⟩
    simp only [parMap]
    apply ext9
    · rw [block11_of_blocks]
    · rw [block12_of_blocks]
    · rw [block13_of_blocks]
    · rw [block21_of_blocks, h21]
    · rw [block22_of_blocks, h22]
    · rw [block23_of_blocks]
    · rw [block31_of_blocks, h31]
    · rw [block32_of_blocks, h32]
    · rw [block33_of_blocks]
end Formalism.FourierDecayAlt.P.S3x1
