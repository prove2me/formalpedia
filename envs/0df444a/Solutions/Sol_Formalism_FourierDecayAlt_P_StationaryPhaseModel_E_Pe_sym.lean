-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_Pe_sym
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:03.307196+00:00
-- url     : https://prove2.me/submissions/6f19f82c-2576-442f-b469-8e963c63e35c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_of_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_Pe_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_Pe_iterated

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
theorem _root_.solution {φ : E → ℝ} {n : ℕ} (h4n : 4 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ σ : ℝ} (hr : 0 < r)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) 4 n ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ n) (E_Pe φ) := by
  have hv := E_P_vanish (hφ.of_le (by exact_mod_cast (by omega : 2 ≤ n))) hc
  have h := Sym.of_vanish (f := E_Pe φ) (M := Γ + Γ * (r + 1) ^ 2) 4 hr hσ hσ1 h4n (E_Pe_contDiff hφ) ?_ ?_
  · exact_mod_cast h
  · intro x hx i hi
    have hx' : -x ∈ Metric.closedBall (0 : E) r := by simpa using hx
    rw [E_Pe_iterated hφ hi, norm_smul]
    have h1 := E_P_bound (by omega) hφ hr hb x hx i hi
    have h2 := E_P_bound (by omega) hφ hr hb (-x) hx' i hi
    have h3 : ‖iteratedFDeriv ℝ i (E_P φ) x + (-1 : ℝ) ^ i • iteratedFDeriv ℝ i (E_P φ) (-x)‖ ≤
        ‖iteratedFDeriv ℝ i (E_P φ) x‖ + ‖iteratedFDeriv ℝ i (E_P φ) (-x)‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      simp
    norm_num
    linarith
  · intro i hi
    rw [E_Pe_iterated hφ (by omega), neg_zero]
    by_cases h3 : i < 3
    · rw [hv i h3]; simp
    · have : i = 3 := by omega
      subst this
      norm_num
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
