-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.gramPos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:44.971945+00:00
-- url     : https://prove2.me/submissions/fae4601e-3997-4246-905f-99993c055b56

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution : GramPos := by
  intro M _ _ R d h x
  constructor
  · rw [Complex.re_sum]; exact Finset.sum_nonneg fun k _ => (h _).1
  · rw [Complex.im_sum]; exact Finset.sum_eq_zero fun k _ => (h _).2
end Formalism.FourierDecayAlt.P.GramProductIdentities
