-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.L2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:07.641507+00:00
-- url     : https://prove2.me/submissions/f0fcb3e5-34a1-4704-9846-83ad203b5dd1

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_ld


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (hTS : ThetaSmooth) (hTR : ThetaRange) (hTL : ThetaLimit) (hTB : ThetaBound) (hC : E.CauchyTheta)
    (B : Base) (σ : ℝ) (h4 : 4 ≤ σ) (p : ℕ) (hp : p ≠ 0) (h : B.Ω → ℂ) (hh : Integrable h B.μ) :
    Tendsto (fun ε : ℝ => ∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * h ω ∂B.μ) (𝓝[>] 0) (𝓝 0) := by
  have hσ : 0 < 4 * σ := by linarith
  have key : Tendsto (fun ε : ℝ => ∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * h ω ∂B.μ) (𝓝[>] 0)
      (𝓝 (∫ _ω, (0:ℂ) ∂B.μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ω => (Real.exp 1 * p.factorial * (4 * σ) ^ p) * ‖h ω‖) ?_ ?_ (hh.norm.const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((Complex.measurable_ofReal.comp
        ((meas_ld p _ (hTS ε σ hε)).comp B.G_meas)).aestronglyMeasurable.mul hh.1)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun ω => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have a := hTB hC σ ε h4 hε p (B.G ω) (B.G_pos ω)
      have b := hTR ε σ (B.G ω) hε (by linarith) (B.G_pos ω)
      calc _ ≤ Real.exp 1 * p.factorial * (4 * σ) ^ p * th ε σ (B.G ω) := a
        _ ≤ Real.exp 1 * p.factorial * (4 * σ) ^ p * 1 := mul_le_mul_of_nonneg_left b.2 (by positivity)
        _ = _ := mul_one _
    · refine Eventually.of_forall fun ω => ?_
      have h0 := hTL σ p (B.G ω) (B.G_pos ω)
      rw [if_neg hp] at h0
      have h1 : Tendsto (fun ε => ((ld p (th ε σ) (B.G ω) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((0:ℝ):ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp h0
      simpa using h1.mul_const (h ω)
  simpa using key
end Formalism.FourierDecayAlt.P.LEx2
