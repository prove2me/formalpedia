-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:39.154798+00:00
-- url     : https://prove2.me/submissions/a6ba7ea2-7929-4f7f-9e11-332a69cf7a4f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_holo_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_T_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_g_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_ev
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_ball_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_mem_ball

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
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hb : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ‖g x‖ ≤ Λ) (c : ℂ) {x : Fin d → ℂ}
    (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) (i : ℕ) {δ : ℝ} (hδ : 0 < δ) (hi : ((i + 1 : ℕ) : ℝ) * δ ≤ r) :
    ‖iteratedFDeriv ℝ i (F_phi d r c g) x‖ ≤ ‖c‖ * (Λ / δ ^ i) := by
  rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) (F_phi_ev (g := g) hr c (F_mem_ball hr hx)) i).eq_of_nhds]
  have hs := F_ball_sub hx hi
  have hx2 : x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := hs (Metric.mem_ball_self (by positivity))
  have h1 := (realPartMulCLM c).norm_iteratedFDeriv_comp_left (n := i)
    ((F_g_contDiffOn hg i).contDiffAt (Metric.isOpen_ball.mem_nhds hx2)) le_rfl
  have h2 := holo_bound i hδ (hg.mono hs) (fun y hy => hb y (hs hy))
  calc _ ≤ ‖realPartMulCLM c‖ * ‖iteratedFDeriv ℝ i g x‖ := h1
    _ ≤ ‖c‖ * (Λ / δ ^ i) := by gcongr; exact F_T_norm c
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
