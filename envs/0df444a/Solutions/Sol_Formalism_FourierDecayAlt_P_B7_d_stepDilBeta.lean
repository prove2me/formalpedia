-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_stepDilBeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:14.003274+00:00
-- url     : https://prove2.me/submissions/ee4552d1-eba8-478b-95da-7dd2e5627548

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_Jtau
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_gq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_weight
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_map_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_emb_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_hsVec_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution : Formalism.FourierDecayAlt.B.StepDilBeta := by
  intro k r Wp Wq _ _ _ _ _ _ D A hJ F _ τ _ t ht
  have h1 : 0 < t.1 := ht.1
  have h2 : 0 < t.2 := ht.2
  set s : ℝ := t.1 * t.2 with hs_def
  have hs : 0 < s := mul_pos h1 h2
  set T := Tz k r D.z
  set T' := Tz k r D.z'
  set f : (Fin r → ℂ) × ℂ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (bcWeight k r T T' q * ‖hsVec (Jtau D (τ.1 * t.1, τ.2 * t.2) F (gq D q))‖ ^ 2) with hf
  have hpt : ∀ q, ENNReal.ofReal (bcWeight k r T T' q * ‖hsVec (Jtau D τ (dilF t F) (gq D q))‖ ^ 2) =
      ENNReal.ofReal ((s ^ kap k r) ^ 2 * (s ^ halfDimensionBlockSummand k r)⁻¹) * f (d_S r s q) := by
    intro q
    rw [d_Jtau D hJ τ t h1 h2 F (gq D q), d_gq D t h1.ne' h2.ne' q, d_hsVec_smul, hf]
    simp only
    rw [d_weight T T' s hs q, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity)]
    congr 1
    field_simp
    rfl
  show (∫⁻ q, ENNReal.ofReal (bcWeight k r T T' q * ‖hsVec (Jtau D τ (dilF t F) (gq D q))‖ ^ 2)) =
    ENNReal.ofReal (s ^ kap k r) * ∫⁻ q, f q
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← (d_emb_S s hs).lintegral_map, d_map_S s hs,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [d_kap]
  field_simp
  ring
end Formalism.FourierDecayAlt.P.B7
