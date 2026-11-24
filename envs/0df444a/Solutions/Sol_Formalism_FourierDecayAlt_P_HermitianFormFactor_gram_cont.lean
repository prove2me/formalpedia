-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.gram_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:55:42.760809+00:00
-- url     : https://prove2.me/submissions/86d3aaf0-bbc0-4f89-99b6-0361c8ca20af

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {Q : Type} [Fintype Q] [DecidableEq Q]
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution : Continuous (fun X : Q → Q → ℂ => (gram X : Q → Q → ℂ)) := by
  have hc : Continuous (fun X : Q → Q → ℂ => cm X) :=
    continuous_matrix fun i j => (continuous_apply i).comp (continuous_apply j)
  exact hc.matrix_conjTranspose.matrix_mul hc
end Formalism.FourierDecayAlt.P.HermitianFormFactor
