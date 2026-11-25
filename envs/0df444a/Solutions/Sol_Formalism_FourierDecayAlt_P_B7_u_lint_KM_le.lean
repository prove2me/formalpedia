-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.u_lint_KM_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:44.720308+00:00
-- url     : https://prove2.me/submissions/f8f4b7c8-4140-44a1-ae6d-1115d88c3e66

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_contOn_of_CkOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_aesm_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_enorm_KM_le
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hCB : CoefBound D Ξ A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ p, D.inSS p → (∫⁻ x, ‖KM D F p x‖ₑ ∂D.μG) ≤
      K * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) * Ξ (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
  obtain ⟨C, hC⟩ := hCB
  obtain ⟨c, hc1, hc2⟩ := hF
  have hcont := contOn_of_CkOn hc1
  have hb : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c := fun g hg =>
    hc2 [] [] (by simp) (by simp) (by simp) g hg
  have hm := u_aesm_F D hcont
  refine ⟨ENNReal.ofReal (‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2) * ENNReal.ofReal (C * c * c),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, fun p hp => ?_⟩
  have hx : Matrix.of p.1.2 * Matrix.of p.1.1 ∈ GV k r := WeylGroupFacts.uh_mul hp.2.1.1 hp.1.1
  have hy : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1
  have h1 := hC F F c c hm hm hb hb _ hx _ hy
  calc (∫⁻ x, ‖KM D F p x‖ₑ ∂D.μG)
      ≤ ∫⁻ x, ENNReal.ofReal (‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2) *
        (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of x * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
          ‖F (Matrix.of x)‖ₑ) ∂D.μG := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem D.haarG] with x hxG
        exact u_enorm_KM_le D F hp hxG
    _ = ENNReal.ofReal (‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2) * ∫⁻ x,
        (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of x * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
          ‖F (Matrix.of x)‖ₑ) ∂D.μG := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2) * (ENNReal.ofReal (C * c * c) *
          Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) * Ξ (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
        gcongr
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.B7
