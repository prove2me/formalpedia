-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.lintegral_weighted_swap_ne_top_and_toReal_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:11:00.973132+00:00
-- url     : https://prove2.me/submissions/96190605-919a-42f5-bfd6-2e527bc01298

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity

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
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution {Tt Q : Type*} [MeasurableSpace Tt] [MeasurableSpace Q] {ν : Measure Tt} {μ : Measure Q}
    [SFinite ν] [SFinite μ]
    (Wt : Tt → ℝ) (hWm : Measurable Wt) (hW0 : ∀ τ, 0 ≤ Wt τ) (w : Q → ℝ) (hwm : Measurable w)
    (hw0 : ∀ q, 0 ≤ w q)
    (n : Tt → Q → ℝ) (hnm : Measurable (fun a : Tt × Q => n a.1 a.2)) (hn0 : ∀ τ q, 0 ≤ n τ q)
    (H : Q → ℂ) (hH : Integrable (fun q => (w q : ℂ) * H q) μ)
    (hgood : ∀ᵐ q ∂μ, w q = 0 ∨
      (Integrable (fun τ => Wt τ * n τ q) ν ∧ ((∫ τ, Wt τ * n τ q ∂ν : ℝ) : ℂ) = H q)) :
    (∫⁻ τ, ENNReal.ofReal (Wt τ) * ∫⁻ q, ENNReal.ofReal (w q * n τ q) ∂μ ∂ν) ≠ ∞ ∧
    (((∫⁻ τ, ENNReal.ofReal (Wt τ) * ∫⁻ q, ENNReal.ofReal (w q * n τ q) ∂μ ∂ν).toReal : ℝ) : ℂ) =
      ∫ q, (w q : ℂ) * H q ∂μ := by
  set B : Q → ℝ := fun q => w q * ∫ τ, Wt τ * n τ q ∂ν with hB
  have hB_eq : ∀ᵐ q ∂μ, ((B q : ℝ) : ℂ) = (w q : ℂ) * H q := by
    filter_upwards [hgood] with q hq
    rcases hq with h | h
    · simp [hB, h]
    · simp only [hB, Complex.ofReal_mul, h.2]
  have hBc : Integrable (fun q => ((B q : ℝ) : ℂ)) μ := hH.congr (hB_eq.mono fun q hq => hq.symm)
  have hBi : Integrable B μ := hBc.re.congr (ae_of_all _ fun q => Complex.ofReal_re _)
  have hB0 : ∀ q, 0 ≤ B q := fun q =>
    mul_nonneg (hw0 q) (integral_nonneg fun τ => mul_nonneg (hW0 τ) (hn0 τ q))
  have hL : (∫⁻ τ, ENNReal.ofReal (Wt τ) * ∫⁻ q, ENNReal.ofReal (w q * n τ q) ∂μ ∂ν) =
      ENNReal.ofReal (∫ q, B q ∂μ) := by
    have s1 : (∫⁻ τ, ENNReal.ofReal (Wt τ) * ∫⁻ q, ENNReal.ofReal (w q * n τ q) ∂μ ∂ν) =
        ∫⁻ τ, ∫⁻ q, ENNReal.ofReal (Wt τ) * ENNReal.ofReal (w q * n τ q) ∂μ ∂ν := by
      refine lintegral_congr fun τ => ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hm : Measurable (Function.uncurry fun (τ : Tt) (q : Q) =>
        ENNReal.ofReal (Wt τ) * ENNReal.ofReal (w q * n τ q)) := by
      have a1 : Measurable fun a : Tt × Q => ENNReal.ofReal (Wt a.1) := (hWm.comp measurable_fst).ennreal_ofReal
      have a2 : Measurable fun a : Tt × Q => ENNReal.ofReal (w a.2 * n a.1 a.2) :=
        ((hwm.comp measurable_snd).mul hnm).ennreal_ofReal
      exact a1.mul a2
    rw [s1, lintegral_lintegral_swap hm.aemeasurable, ofReal_integral_eq_lintegral_ofReal hBi (ae_of_all _ hB0)]
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with q hq
    rcases hq with h | h
    · simp [hB, h]
    · have e : ∀ τ, ENNReal.ofReal (Wt τ) * ENNReal.ofReal (w q * n τ q) =
          ENNReal.ofReal (w q * (Wt τ * n τ q)) := by
        intro τ
        rw [← ENNReal.ofReal_mul (hW0 τ)]
        congr 1
        ring
      simp_rw [e]
      rw [← ofReal_integral_eq_lintegral_ofReal (h.1.const_mul _)
        (ae_of_all _ fun τ => mul_nonneg (hw0 q) (mul_nonneg (hW0 τ) (hn0 τ q))), integral_const_mul]
  rw [hL]
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  rw [ENNReal.toReal_ofReal (integral_nonneg hB0), ← integral_complex_ofReal]
  exact integral_congr_ae hB_eq
end Formalism.FourierDecayAlt.P.B7
