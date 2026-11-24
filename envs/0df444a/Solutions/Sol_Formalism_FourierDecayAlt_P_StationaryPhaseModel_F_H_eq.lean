-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_H_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:28.045994+00:00
-- url     : https://prove2.me/submissions/cff2e86a-6f67-40a5-81b1-133d17f8c475

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_hasFDerivAt_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_dg_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {r : ℝ} {g : (Fin d → ℂ) → ℂ}
variable {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) (i j : Fin d) :
    fderiv ℂ (fderiv ℂ g) 0 (Pi.single j 1) (Pi.single i 1) = H i j := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.mem_ball_self (by positivity)
  have h1 : HasDerivAt (fun ξ : ℂ => Function.update (0 : Fin d → ℂ) j ξ) (Pi.single j (1:ℂ)) 0 :=
    hasDerivAt_update (0 : Fin d → ℂ) j 0
  have hu0 : Function.update (0 : Fin d → ℂ) j 0 = 0 := by
    simp
  have h2 : HasFDerivAt (fun y => fderiv ℂ g y (Pi.single i 1))
      ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).comp (fderiv ℂ (fderiv ℂ g) 0))
      (Function.update (0 : Fin d → ℂ) j 0) := by
    rw [hu0]; exact F_hasFDerivAt_apply hr hg _
  have h3 := h2.comp_hasDerivAt (0:ℂ) h1
  have hev : (fun ξ => dg (Function.update 0 j ξ) i) =ᶠ[𝓝 (0:ℂ)]
      ((fun y => fderiv ℂ g y (Pi.single i 1)) ∘ fun ξ : ℂ => Function.update (0 : Fin d → ℂ) j ξ) := by
    have hc : ContinuousAt (fun ξ : ℂ => Function.update (0 : Fin d → ℂ) j ξ) 0 := h1.continuousAt
    have : ∀ᶠ ξ in 𝓝 (0:ℂ), Function.update (0 : Fin d → ℂ) j ξ ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) :=
      hc.eventually_mem (by rw [hu0]; exact Metric.isOpen_ball.mem_nhds h0)
    filter_upwards [this] with ξ hξ
    exact (F_dg_eq hg hdg hξ i).symm
  exact (h3.congr_of_eventuallyEq hev).unique (hH i j)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
