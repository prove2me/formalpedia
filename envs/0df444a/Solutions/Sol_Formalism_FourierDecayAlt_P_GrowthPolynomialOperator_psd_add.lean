-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.psd_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:25.309174+00:00
-- url     : https://prove2.me/submissions/90cfee9d-f6ac-4126-8257-d33e111eba5e

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution {α : Type} {Y : Finset α} {k k' : α → α → ℂ}
    (hk : TB.PSDOn Y k) (hk' : TB.PSDOn Y k') : TB.PSDOn Y (fun x y => k x y + k' x y) := by
  have e : (Matrix.of fun x y : Y => k x y + k' x y) =
      (Matrix.of fun x y : Y => k x y) + Matrix.of fun x y : Y => k' x y := by
    ext x y
    simp [Matrix.of_apply]
  show Matrix.PosSemidef (Matrix.of fun x y : Y => k x y + k' x y)
  rw [e]
  exact Matrix.PosSemidef.add hk hk'
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
