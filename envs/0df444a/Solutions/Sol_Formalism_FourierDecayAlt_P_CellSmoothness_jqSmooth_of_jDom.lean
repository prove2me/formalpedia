-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CellSmoothness.jqSmooth_of_jDom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:48.823589+00:00
-- url     : https://prove2.me/submissions/e332469f-031b-485e-8700-37f0081d72a8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CellSmoothness
import Theorems.Thm_Formalism_FourierDecayAlt_P_CellSmoothness_jqSmooth_of_words
import Theorems.Thm_Formalism_FourierDecayAlt_P_bessel_words_of_domain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CellSmoothness
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CellSmoothness
theorem _root_.solution (hD : JDom) : JqSmooth := jqSmooth_of_words (bessel_words_of_domain hD)
end Formalism.FourierDecayAlt.P.CellSmoothness
