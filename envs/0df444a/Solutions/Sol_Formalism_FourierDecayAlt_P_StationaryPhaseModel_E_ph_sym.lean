-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_ph_sym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:58.556626+00:00
-- url     : https://prove2.me/submissions/de92f868-3d9c-45ff-a5cc-5c2748a789aa

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_const_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_hess_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_dphi_sym
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_wt_pos

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
theorem _root_.solution {φ : E → ℝ} {N : ℕ} (hN : 1 ≤ N) (hφ : ContDiff ℝ (N + 1 : ℕ) φ) {r Γ σ : ℝ} (hr : 0 < r)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N + 1 → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) 1 N (Γ + Γ * (r + 1) ^ N)
      (fderiv ℝ (fun y => quad φ y + s * E_P φ y)) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact_mod_cast (by omega : 2 ≤ N + 1))
  rw [E_ph_fderiv hφ2]
  have h1 := Sym.const_smul (1 - s)
    (Sym.clm (A := Metric.closedBall (0 : E) r) (N := N) (fderiv ℝ (fderiv ℝ φ) 0) hσ)
  have h2 := Sym.const_smul s (E_dphi_sym hN hφ hr hσ hσ1 hc hb)
  have hB := E_hess_le (by omega : 2 ≤ N + 1) hr hb
  have hΓ : 0 ≤ Γ := (norm_nonneg _).trans hB
  refine Sym.mono (fun x _ => E_wt_pos hσ x) (h1.add h2) le_rfl ?_
  have a1 : |1 - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have a2 : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have p : 0 ≤ Γ * (r + 1) ^ N := by positivity
  have e1 : |1 - s| * ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ 1 * Γ := mul_le_mul a1 hB (norm_nonneg _) zero_le_one
  have e2 : |s| * (Γ * (r + 1) ^ N) ≤ 1 * (Γ * (r + 1) ^ N) := mul_le_mul_of_nonneg_right a2 p
  linarith
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
