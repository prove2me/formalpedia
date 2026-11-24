-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.gauss_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:34:58.185483+00:00
-- url     : https://prove2.me/submissions/edc883c9-7e5b-45b6-8e34-0ef12bbb4d75

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCStmt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Lemmata_GeneralBFactRightSide_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBCLat

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
theorem _root_.solution (m n : ℤ) (h : (m : ℂ) + (n : ℂ) * Complex.I ≠ 0) :
    1 ≤ ‖(m : ℂ) + (n : ℂ) * Complex.I‖ := by
  have hmn : m ≠ 0 ∨ n ≠ 0 := by
    by_contra hc; push Not at hc; apply h; simp [hc.1, hc.2]
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    rcases hmn with hm | hn
    · have : (1 : ℤ) ≤ m ^ 2 := by nlinarith [Int.one_le_abs hm, sq_abs m]
      have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast this
      nlinarith [sq_nonneg (n : ℝ)]
    · have : (1 : ℤ) ≤ n ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs n]
      have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast this
      nlinarith [sq_nonneg (m : ℝ)]
  rw [← Real.sqrt_one, Complex.norm_def, Complex.normSq_apply]
  apply Real.sqrt_le_sqrt
  simp; nlinarith
end Formalism.FourierDecayAlt.P.PBC.Lat
