-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_dphi_sym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:13.066888+00:00
-- url     : https://prove2.me/submissions/41e19725-c8d1-4531-a166-6c2a83629fd3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_of_vanish

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
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N + 1 → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) 1 N (Γ * (r + 1) ^ N) (fderiv ℝ φ) := by
  have h := Sym.of_vanish (f := fderiv ℝ φ) (M := Γ) 1 hr hσ hσ1 hN
    (hφ.fderiv_right (by exact_mod_cast le_rfl)) ?_ ?_
  · exact_mod_cast h
  · intro x hx i hi
    rw [norm_iteratedFDeriv_fderiv]
    exact hb x hx (i + 1) (by omega)
  · intro i hi
    have : i = 0 := by omega
    subst this
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero, hc, norm_zero]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
