-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.lev_act_iL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:26:26.552551+00:00
-- url     : https://prove2.me/submissions/7ef7c846-38c7-4423-baf5-8c95bfa45d64

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_row_iL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (ιLev k 1 r' g *ᵥ u) (iL k r') = u (iL k r') := by
  simp [mulVec, dotProduct, lev_row_iL]
end Formalism.FourierDecayAlt.P.B2x5
