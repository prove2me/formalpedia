-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_P_fderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:47.200746+00:00
-- url     : https://prove2.me/submissions/3e0dee0c-8782-41f2-a79d-8550abd20608

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_sym

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {φ : E → ℝ} {n : ℕ} (h3n : 3 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ : ℝ} (hr : 0 < r)
    (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ)
    {x : E} (hx : x ∈ Metric.closedBall (0 : E) r) :
    ‖fderiv ℝ (E_P φ) x‖ ≤ (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n * ‖x‖ ^ 2 := by
  set K := (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n with hK
  have ht : Tendsto (fun σ : ℝ => K * (‖x‖ + σ) ^ 2) (𝓝[>] 0) (𝓝 (K * (‖x‖ + 0) ^ 2)) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact (Continuous.tendsto (by fun_prop) 0)
  rw [add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with σ hσ
  have h := (E_P_sym h3n hφ hr hσ.1 hσ.2 hc hb).2 x hx 1 (by omega)
  rw [norm_iteratedFDeriv_one] at h
  have h2 : wt σ x ^ ((3 : ℤ) - ((1 : ℕ) : ℤ)) = (‖x‖ + σ) ^ 2 := by
    norm_num [wt]
  rwa [h2] at h
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
