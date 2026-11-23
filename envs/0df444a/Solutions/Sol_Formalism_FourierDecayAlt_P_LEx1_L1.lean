-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.L1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:42.805899+00:00
-- url     : https://prove2.me/submissions/3f33d2ee-b882-40dc-b366-a6d5758ea933

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_meas_th

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
theorem _root_.solution (hTR : ThetaRange) (hTL : ThetaLimit) (B : Base) (σ : ℝ) (hσ : 0 ≤ σ) (f : B.Ω → ℝ)
    (hf : Integrable f B.μ) :
    Tendsto (fun ε : ℝ => ∫ ω, th ε σ (B.G ω) * f ω ∂B.μ) (𝓝[>] 0) (𝓝 (∫ ω, f ω ∂B.μ)) := by
  have lim : ∀ ω, Tendsto (fun ε : ℝ => th ε σ (B.G ω) * f ω) (𝓝[>] 0) (𝓝 (f ω)) := by
    intro ω
    have h0 := hTL σ 0 (B.G ω) (B.G_pos ω)
    simp only [ld, iteratedDeriv_zero, Real.exp_log (B.G_pos ω), ↓reduceIte] at h0
    simpa using h0.mul_const (f ω)
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => ‖f ω‖) ?_ ?_ hf.norm
    (ae_of_all _ lim)
  · exact Filter.Eventually.of_forall fun ε =>
      (meas_th B ε σ).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine ae_of_all _ fun ω => ?_
    obtain ⟨h1, h2⟩ := hTR ε σ (B.G ω) hε hσ (B.G_pos ω)
    rw [norm_mul, Real.norm_of_nonneg h1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) h2
end Formalism.FourierDecayAlt.P.LEx1
