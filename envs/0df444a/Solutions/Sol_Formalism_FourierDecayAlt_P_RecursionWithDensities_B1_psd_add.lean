-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.psd_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:39.464548+00:00
-- url     : https://prove2.me/submissions/855739a1-36a8-43c0-bbc3-cebce39f85d4

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution {α : Type} {Y : Finset α} {k k' : α → α → ℂ} (h : PSDOn Y k) (h' : PSDOn Y k') :
    PSDOn Y (fun x y => k x y + k' x y) := by
  unfold TB.PSDOn at h h' ⊢
  have e : (Matrix.of fun x y : Y => k x y + k' x y) =
      (Matrix.of fun x y : Y => k x y) + Matrix.of fun x y : Y => k' x y := by
    ext x y
    simp
  rw [e]
  exact h.add h'
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
