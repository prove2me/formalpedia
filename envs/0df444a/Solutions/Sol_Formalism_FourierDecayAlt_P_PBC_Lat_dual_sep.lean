-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.dual_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:11:53.881523+00:00
-- url     : https://prove2.me/submissions/9ab7b443-6e64-4d4b-8f3b-df9234ae85f0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_mem_dual_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBC_Lat_gauss_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBC
open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped Pointwise
noncomputable section
open Classical
open Formalism.FourierDecayAlt.P.PBC.Lat
namespace Formalism.FourierDecayAlt.P.PBC.Lat
theorem _root_.solution (f : ℕ) (R : ℝ) (hR : 0 < R) (σ σ' : crystallineComparison.V f) (hσ : σ ∈ crystallineComparison.dualSet (Lstd f R))
    (hσ' : σ' ∈ crystallineComparison.dualSet (Lstd f R)) (hne : σ ≠ σ') : 1 / (2 * R) ≤ ‖σ - σ'‖ := by
  obtain ⟨v, hv⟩ : ∃ v, σ v ≠ σ' v := by
    by_contra h; push Not at h; exact hne (funext h)
  obtain ⟨a, b, hab⟩ := (mem_dual_iff f R hR σ).1 hσ v
  obtain ⟨a', b', hab'⟩ := (mem_dual_iff f R hR σ').1 hσ' v
  have hR' : (2 * (R : ℂ)) ≠ 0 := by simp [hR.ne']
  have hd : σ v - σ' v = (((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I) / (2 * (R : ℂ)) := by
    rw [hab, hab']; push_cast; field_simp; ring
  have hnz : (((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I) ≠ 0 := by
    intro h0; apply hv; rw [← sub_eq_zero, hd, h0, zero_div]
  calc 1 / (2 * R) ≤ ‖(((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I)‖ / (2 * R) :=
        div_le_div_of_nonneg_right (gauss_norm _ _ hnz) (by positivity)
    _ = ‖σ v - σ' v‖ := by
        rw [hd, norm_div]; congr 1; simp [abs_of_pos hR]
    _ = ‖(σ - σ') v‖ := rfl
    _ ≤ ‖σ - σ'‖ := norm_le_pi_norm (σ - σ') v
end Formalism.FourierDecayAlt.P.PBC.Lat
