-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.integrable_test_weighted_phase_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:55:27.792636+00:00
-- url     : https://prove2.me/submissions/4387ad1b-4e5f-4a2d-97e9-4605f46ee967

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_product_test_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regularised_kernel_integrable

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) (p : SS k r) :
    Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) *
      (Bt D F F' (p, x.2) * Complex.exp (Complex.I * (phase D x.1 p x.2 : ℂ))))
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) := by
  have hb : Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => (|w₁ x.1.1| * |w₂ x.1.2|) * ‖Bt D F F' (p, x.2)‖)
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure (ℝ × ℝ))) :=
    Integrable.mul_prod (f := fun τ : ℝ × ℝ => |w₁ τ.1| * |w₂ τ.2|)
      (g := fun t : ℝ × ℝ => ‖Bt D F F' (p, t)‖)
      (product_test_integrable h₁ h₂) (regularised_kernel_integrable H hF hF' p).norm
  have h1c := h₁.1.continuous
  have h2c := h₂.1.continuous
  have hBc := Bt_continuous H hF hF' p
  have hph : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => phase D x.1 p x.2 := by
    unfold phase; fun_prop
  have hcont : Continuous (fun x : (ℝ × ℝ) × (ℝ × ℝ) => ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) *
      (Bt D F F' (p, x.2) * Complex.exp (Complex.I * (phase D x.1 p x.2 : ℂ)))) := by
    have hB2 : Continuous fun x : (ℝ × ℝ) × (ℝ × ℝ) => Bt D F F' (p, x.2) := hBc.comp continuous_snd
    fun_prop
  refine hb.mono' hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
end Formalism.FourierDecayAlt.P.B6
