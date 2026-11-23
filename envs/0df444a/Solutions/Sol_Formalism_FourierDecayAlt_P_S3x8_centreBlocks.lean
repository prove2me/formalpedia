-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.centreBlocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:20.300104+00:00
-- url     : https://prove2.me/submissions/337daefd-a0b2-4a59-b676-14fb5859ec15

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure

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
theorem _root_.solution : CentreBlocks := by
  intro F _ r ϖ j₁₁ j₁₃ j₃₃ X S S' hϖ hX
  have h1 : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hX
  have h2 : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hX
  have e1 : (j₁₁ - ϖ • (S * X)) * X⁻¹ = j₁₁ * X⁻¹ - ϖ • S := by
    rw [sub_mul, smul_mul_assoc, mul_assoc, h1, mul_one]
  have e3 : j₁₁ * X⁻¹ * (X * S') = j₁₁ * S' := by rw [mul_assoc, ← mul_assoc X⁻¹, h2, one_mul]
  have e2 : (j₁₁ * X⁻¹ - ϖ • S) * (j₃₃ + ϖ • (X * S')) - j₁₁ * X⁻¹ * j₃₃
      = ϖ • (j₁₁ * S' - S * j₃₃ - S * (ϖ • X) * S') := by
    simp only [sub_mul, mul_add, mul_smul_comm, smul_mul_assoc, e3, smul_sub, mul_assoc]; abel
  rw [e1, e2, smul_smul, inv_mul_cancel₀ hϖ, one_smul, sub_mul]; abel
end Formalism.FourierDecayAlt.P.S3x8
