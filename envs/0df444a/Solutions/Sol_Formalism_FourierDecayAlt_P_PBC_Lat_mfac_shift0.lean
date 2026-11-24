-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.mfac_shift0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:54:01.017488+00:00
-- url     : https://prove2.me/submissions/3c21f411-8755-446f-842b-02a93eed4034

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
theorem _root_.solution (K : ℕ) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    crystallineComparison.mfac K L a ≤ crystallineComparison.mfac K (L + δ) (a + δ) := by
  have had : 0 < a + δ := by linarith
  unfold crystallineComparison.mfac
  rw [if_neg had.ne']
  split_ifs with h0
  · subst h0
    rw [min_eq_left (one_le_pow₀ ((one_le_div (by linarith)).mpr (by linarith)))]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    rcases le_or_gt a L with haL | haL
    · rw [min_eq_left (one_le_pow₀ ((one_le_div had).mpr (by linarith)))]
      exact min_le_left _ _
    · apply min_le_min_left
      apply pow_le_pow_left₀ (div_nonneg hL ha)
      rw [div_le_div_iff₀ hapos had]
      nlinarith
end Formalism.FourierDecayAlt.P.PBC.Lat
