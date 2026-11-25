-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.gN_mul_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:43:23.424869+00:00
-- url     : https://prove2.me/submissions/df03301d-7977-4b63-869e-a03e1edd4e46

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNMulRpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_uh_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution (hNI : NormInv) {x Y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hY : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ} (hb : 0 ≤ b) :
    B.gN (Y * x) ^ (-b) ≤ B.gN x ^ b * B.gN Y ^ (-b) := by
  obtain ⟨hsub, hinv⟩ := hNI k r
  have hxi := MatrixMultiplicationContinuity.uh_inv hx
  have hYx : Y * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hY hx
  have h1 : 1 ≤ B.gN x := (hinv x hx).2
  have h2 : 1 ≤ B.gN Y := (hinv Y hY).2
  have h3 : 1 ≤ B.gN (Y * x) := (hinv _ hYx).2
  have hle : B.gN Y ≤ B.gN (Y * x) * B.gN x := by
    have e : Y = Y * x * x⁻¹ := by rw [Matrix.mul_assoc, hxi.2.1, Matrix.mul_one]
    calc B.gN Y = B.gN (Y * x * x⁻¹) := by rw [← e]
      _ ≤ B.gN (Y * x) * B.gN x⁻¹ := hsub _ _
      _ = B.gN (Y * x) * B.gN x := by rw [(hinv x hx).1]
  have hpos : 0 < B.gN x := lt_of_lt_of_le one_pos h1
  have hq : B.gN Y / B.gN x ≤ B.gN (Y * x) := (div_le_iff₀ hpos).mpr hle
  have hqpos : 0 < B.gN Y / B.gN x := div_pos (lt_of_lt_of_le one_pos h2) hpos
  calc B.gN (Y * x) ^ (-b) ≤ (B.gN Y / B.gN x) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hqpos hq (by linarith)
    _ = B.gN x ^ b * B.gN Y ^ (-b) := by
        rw [Real.div_rpow (lt_of_lt_of_le one_pos h2).le hpos.le, Real.rpow_neg hpos.le,
          div_eq_mul_inv, inv_inv, mul_comm]
end Formalism.FourierDecayAlt.P.S3dx4
