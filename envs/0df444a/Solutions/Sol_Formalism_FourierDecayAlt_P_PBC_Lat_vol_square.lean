-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBC.Lat.vol_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:06:59.99383+00:00
-- url     : https://prove2.me/submissions/c5d149c9-7dce-4cd1-bb90-3f6f56408593

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
theorem _root_.solution : (volume : Measure ℂ) {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1} = 1 := by
  have h : {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1} =
      Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z; simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet), Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ico]
  simp
end Formalism.FourierDecayAlt.P.PBC.Lat
