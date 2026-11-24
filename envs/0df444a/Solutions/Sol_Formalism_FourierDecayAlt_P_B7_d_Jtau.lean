-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_Jtau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:43:34.783227+00:00
-- url     : https://prove2.me/submissions/39099788-5f6d-4d6f-adf9-66e3eede7b04

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_ae_uw
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_dilE_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_map_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_rho

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (hJ : DilJac D) (τ t : ℝ × ℝ) (h1 : 0 < t.1) (h2 : 0 < t.2)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    Jtau D τ (dilF t F) g = ((t.1 * t.2) ^ kap k r : ℝ) •
      Jtau D (τ.1 * t.1, τ.2 * t.2) F ((aDil k r t.1)⁻¹ * g * aDil k r t.2) := by
  have hc : ((t.1 * t.2) ^ kap k r : ℝ) ≠ 0 := (pow_pos (mul_pos h1 h2) _).ne'
  have hm := d_map_dil D hJ t h1 h2
  have e1 : (∫ p, xiTau D τ p • rho D p (dilF t F) g ∂(D.μSS.map (d_dilE t h1.ne' h2.ne'))) =
      ∫ p, xiTau D (τ.1 * t.1, τ.2 * t.2) p • rho D p F ((aDil k r t.1)⁻¹ * g * aDil k r t.2) ∂D.μSS := by
    rw [integral_map_equiv]
    refine integral_congr_ae ?_
    filter_upwards [d_ae_uw D] with p hp
    rw [d_dilE_apply, d_xi D τ t h1.ne' h2.ne', d_rho D t h1.ne' h2.ne' F g p hp.1 hp.2]
  unfold Jtau
  rw [← e1, hm, integral_smul_measure, smul_smul]
  have : ((t.1 * t.2) ^ kap k r : ℝ) *
      (ENNReal.ofReal ((t.1 ^ kap k r)⁻¹) * ENNReal.ofReal ((t.2 ^ kap k r)⁻¹)).toReal = 1 := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
      mul_pow]
    field_simp
  rw [this, one_smul]
end Formalism.FourierDecayAlt.P.B7
