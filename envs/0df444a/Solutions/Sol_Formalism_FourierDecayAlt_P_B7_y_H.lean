-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.y_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:28.28065+00:00
-- url     : https://prove2.me/submissions/dd8090b6-d5fb-4007-a055-863273a282eb

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_PhiM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_map_Phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_boundary_weight_nonneg

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
attribute [local instance] sfNu
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) {G : Mt k r → ℂ} (hG : Integrable G D.μG) :
    Integrable (fun q => ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) *
      ∫ p, G (PhiM D (q, p)) ∂D.μSS) volume ∧
    (∫ q, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) * ∫ p, G (PhiM D (q, p)) ∂D.μSS) =
      ∫ x, G x ∂D.μG := by
  have hmap := map_Phi D hI
  have hPm := measurable_PhiM D
  have hG' : Integrable G (((nuQ D).prod D.μSS).map (PhiM D)) := by rw [hmap]; exact hG
  have hc : Integrable (fun a => G (PhiM D a)) ((nuQ D).prod D.μSS) :=
    (integrable_map_measure hG'.1 hPm.aemeasurable).1 hG'
  have hHν : Integrable (fun q => ∫ p, G (PhiM D (q, p)) ∂D.μSS) (nuQ D) := hc.integral_prod_left
  have hint : (∫ q, ∫ p, G (PhiM D (q, p)) ∂D.μSS ∂(nuQ D)) = ∫ x, G x ∂D.μG := by
    rw [← integral_prod (fun a => G (PhiM D a)) hc, ← hmap, integral_map hPm.aemeasurable hG'.1]
  have hf : Measurable fun q => ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) :=
    (measurable_bcWeight _ _).ennreal_ofReal
  have hflt : ∀ᵐ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) < ∞ :=
    ae_of_all _ fun q => ENNReal.ofReal_lt_top
  have e : ∀ q : (Fin r → ℂ) × ℂ, (ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q)).toReal •
      (∫ p, G (PhiM D (q, p)) ∂D.μSS) =
      ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) * ∫ p, G (PhiM D (q, p)) ∂D.μSS := by
    intro q
    rw [ENNReal.toReal_ofReal (boundary_weight_nonneg _ _ q), Complex.real_smul]
  constructor
  · have := (integrable_withDensity_iff_integrable_smul' hf hflt).1 hHν
    exact this.congr (ae_of_all _ e)
  · rw [← hint]
    unfold nuQ
    rw [integral_withDensity_eq_integral_toReal_smul hf hflt]
    exact integral_congr_ae (ae_of_all _ fun q => (e q).symm)
end Formalism.FourierDecayAlt.P.B7
