-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_osc_quad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:10.495968+00:00
-- url     : https://prove2.me/submissions/d9c1883c-cd2e-41ca-b55f-639f2a7bd84c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_B_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_bump_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_psi_eq

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
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ} {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0)
    (β : ℂ) {t : ℂ} (ht : t ≠ 0) (x : Fin d → ℂ) :
    osc (quad (F_phi d r (F_c β t) g)) ‖t‖ x = psi β (g 0 / t) * psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.closedBall (0 : Fin d → ℂ) (5 * r / 4) :=
    Metric.mem_closedBall_self (by positivity)
  have e1 : (x ⬝ᵥ (H *ᵥ x)) / (2 * t) = ((x ⬝ᵥ (H *ᵥ x)) / 2) / t := by
    rw [div_div]
  rw [e1, F_psi_eq β ht, F_psi_eq β ht, ← Complex.exp_add]
  unfold osc quad
  rw [F_phi_snd hr hg, F_B_eq hr hg hdg hH]
  congr 1
  rw [← mul_add, ← Complex.ofReal_add]
  congr 2
  have e2 : F_phi d r (F_c β t) g 0 = (F_c β t * g 0).re := by
    unfold F_phi; rw [F_bump_one hr h0, one_mul]
  have e3 : (F_c β t * ((x ⬝ᵥ (H *ᵥ x)) / 2)).re = (1 / 2) * (F_c β t * (x ⬝ᵥ (H *ᵥ x))).re := by
    have : F_c β t * ((x ⬝ᵥ (H *ᵥ x)) / 2) = ((1 / 2 : ℝ) : ℂ) * (F_c β t * (x ⬝ᵥ (H *ᵥ x))) := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  rw [e2, e3]
  ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
