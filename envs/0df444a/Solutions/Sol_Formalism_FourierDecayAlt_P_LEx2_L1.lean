-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.L1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:57.641605+00:00
-- url     : https://prove2.me/submissions/55d1ce8e-f008-4ad6-8c10-f21cf6ff654f

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_meas_th__13e6d05155eb
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_ld_zero__1805213b0513


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
theorem _root_.solution (hTR : ThetaRange) (hTL : ThetaLimit) (B : Base) (σ : ℝ) (hσ : 0 ≤ σ) (f : B.Ω → ℝ)
    (hf : Integrable f B.μ) :
    Tendsto (fun ε : ℝ => ∫ ω, th ε σ (B.G ω) * f ω ∂B.μ) (𝓝[>] 0) (𝓝 (∫ ω, f ω ∂B.μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => ‖f ω‖) ?_ ?_ hf.norm ?_
  · exact Eventually.of_forall fun ε => ((meas_th' B ε σ).aestronglyMeasurable.mul hf.1)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun ω => ?_
    have h := hTR ε σ (B.G ω) hε hσ (B.G_pos ω)
    rw [norm_mul, Real.norm_of_nonneg h.1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) h.2
  · refine Eventually.of_forall fun ω => ?_
    have h := hTL σ 0 (B.G ω) (B.G_pos ω)
    have h' : Tendsto (fun ε => th ε σ (B.G ω)) (𝓝[>] 0) (𝓝 1) := by
      simpa [ld_zero' _ _ (B.G_pos ω)] using h
    simpa using h'.mul_const (f ω)
end Formalism.FourierDecayAlt.P.LEx2
