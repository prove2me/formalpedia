-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.continuous_critCut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:15.274786+00:00
-- url     : https://prove2.me/submissions/76bed3af-70a0-45ab-a39e-5e4d49d20bdd

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_continuous_cyclotomic_character

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution {n : ℕ} (δ : ℝ) (z : ℂ) : Continuous (critCut (n := n) δ z) := by
  unfold critCut
  exact continuous_finsetProd _ fun k _ => continuous_cyclotomic_character.comp (by fun_prop)
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
