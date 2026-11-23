-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.pointwise_stabiliser_parametrisation_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:52.352275+00:00
-- url     : https://prove2.me/submissions/76453aa3-a834-4058-b2e2-61db79465c3b

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
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution : Function.Bijective (pointwiseStabiliserParametrisation (A := A) (r := r) (k := k)) := by
  constructor
  · rintro ⟨⟨h, hh⟩, b, c, e⟩ ⟨⟨h', hh'⟩, b', c', e'⟩ E
    have E' := congrArg Subtype.val E
    simp only [pointwiseStabiliserParametrisation] at E'
    have e12 := congrArg b12 E'
    have e13 := congrArg b13 E'
    have e22 := congrArg b22 E'
    have e23 := congrArg b23 E'
    rw [block12_of_blocks, block12_of_blocks] at e12
    rw [block13_of_blocks, block13_of_blocks] at e13
    rw [block22_of_blocks, block22_of_blocks] at e22
    rw [block23_of_blocks, block23_of_blocks] at e23
    have e22' := midEmb_inj e22
    have e12' := (Matrix.fromCols_inj e12).1
    have e23' := (Matrix.fromRows_inj e23).1
    subst e12' e13 e22' e23'
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨⟨-, -, h21, h31, h32, h, hh, h22⟩, x11, x33, x12, x23⟩ := (mem_pointwise_stabiliser_iff x).1 hx
    refine ⟨⟨⟨h, hh⟩, (b12 x).toCols₁, b13 x, (b23 x).toRows₁⟩, Subtype.ext ?_⟩
    simp only [pointwiseStabiliserParametrisation]
    apply ext9
    · rw [block11_of_blocks, x11]
    · rw [block12_of_blocks]
      ext a j
      rcases j with j | j
      · simp [Matrix.toCols₁]
      · simp [x12 a]
    · rw [block13_of_blocks]
    · rw [block21_of_blocks, h21]
    · rw [block22_of_blocks, h22]
    · rw [block23_of_blocks]
      ext j b
      rcases j with j | j
      · simp [Matrix.toRows₁]
      · simp [x23 b]
    · rw [block31_of_blocks, h31]
    · rw [block32_of_blocks, h32]
    · rw [block33_of_blocks, x33]
end Formalism.FourierDecayAlt.P.S3x1
