-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.L2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:30.302732+00:00
-- url     : https://prove2.me/submissions/83888725-f128-4b42-9e6f-15b943dca5c3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (hTS : ThetaSmooth) (hTR : ThetaRange) (hTL : ThetaLimit) (hTB : ThetaBound) (hC : E.CauchyTheta)
    (B : Base) (σ : ℝ) (h4 : 4 ≤ σ) (p : ℕ) (hp : p ≠ 0) (h : B.Ω → ℂ) (hh : Integrable h B.μ) :
    Tendsto (fun ε : ℝ => ∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * h ω ∂B.μ) (𝓝[>] 0) (𝓝 0) := by
  have hσ : 0 ≤ σ := by linarith
  have lim : ∀ ω, Tendsto (fun ε : ℝ => (ld p (th ε σ) (B.G ω) : ℂ) * h ω) (𝓝[>] 0) (𝓝 0) := by
    intro ω
    have h0 := hTL σ p (B.G ω) (B.G_pos ω)
    rw [if_neg hp] at h0
    have h1 := ((Complex.continuous_ofReal.tendsto 0).comp h0).mul_const (h ω)
    simpa using h1
  have hK : 0 ≤ Real.exp 1 * p.factorial * (4 * σ) ^ p :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith) p)
  have hmeas : ∀ ε : ℝ, Measurable fun ω => ld p (th ε σ) (B.G ω) := by
    intro ε
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    have hm : Measurable (iteratedDeriv (q + 1) (fun u => th ε σ (Real.exp u))) := by
      rw [iteratedDeriv_succ]
      exact measurable_deriv _
    unfold ld
    exact hm.comp (Real.measurable_log.comp B.G_meas)
  have key := tendsto_integral_filter_of_dominated_convergence (μ := B.μ) (l := 𝓝[>] (0:ℝ))
    (F := fun ε ω => (ld p (th ε σ) (B.G ω) : ℂ) * h ω) (f := fun _ => (0:ℂ))
    (fun ω => Real.exp 1 * p.factorial * (4 * σ) ^ p * ‖h ω‖)
    (Filter.Eventually.of_forall fun ε =>
      (Complex.measurable_ofReal.comp (hmeas ε)).aestronglyMeasurable.mul hh.aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      refine ae_of_all _ fun ω => ?_
      have hb := hTB hC σ ε h4 hε p (B.G ω) (B.G_pos ω)
      obtain ⟨_, h2⟩ := hTR ε σ (B.G ω) hε hσ (B.G_pos ω)
      have h3 : |ld p (th ε σ) (B.G ω)| ≤ Real.exp 1 * p.factorial * (4 * σ) ^ p := by
        calc _ ≤ _ := hb
          _ ≤ Real.exp 1 * p.factorial * (4 * σ) ^ p * 1 := mul_le_mul_of_nonneg_left h2 hK
          _ = _ := mul_one _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
    (hh.norm.const_mul _) (ae_of_all _ lim)
  simpa using key
end Formalism.FourierDecayAlt.P.LEx1
