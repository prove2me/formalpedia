-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.psd_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:45.015622+00:00
-- url     : https://prove2.me/submissions/0e10b7a2-bb73-444e-8dc1-f811fd1671ae

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
theorem _root_.solution {α : Type} {Y : Finset α} {k : α → α → ℂ} (c : ℝ) (hc : 0 ≤ c) (h : PSDOn Y k) :
    PSDOn Y (fun x y => (c : ℂ) * k x y) := by
  unfold TB.PSDOn at h ⊢
  have e : (Matrix.of fun x y : Y => (c : ℂ) * k x y) = (c : ℂ) • Matrix.of fun x y : Y => k x y := by
    ext x y
    simp
  rw [e]
  exact h.smul (Complex.zero_le_real.mpr hc)
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
