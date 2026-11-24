-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_P_sym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:01.436265+00:00
-- url     : https://prove2.me/submissions/a47acc01-7ea2-44a7-bedb-d9afed825dc9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_of_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_bound

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
theorem _root_.solution {φ : E → ℝ} {n : ℕ} (h3n : 3 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ σ : ℝ} (hr : 0 < r)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) 3 n ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n) (E_P φ) := by
  have h := Sym.of_vanish (f := E_P φ) 3 hr hσ hσ1 h3n (E_P_contDiff hφ) (E_P_bound (by omega) hφ hr hb)
    (E_P_vanish (hφ.of_le (by exact_mod_cast (by omega : 2 ≤ n))) hc)
  exact_mod_cast h
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
