-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.lev_act_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:26:27.999899+00:00
-- url     : https://prove2.me/submissions/44d7723f-c32d-4c4e-bcbd-1c40a14a998c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_sum_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_levi_entry_first_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_lev_iL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_lev_lev

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
    res k r' (ιLev k 1 r' g *ᵥ u) = g *ᵥ res k r' u := by
  funext j
  simp only [res, mulVec, dotProduct]
  rw [sum_split k r']
  simp [levi_entry_first_zero, lev_lev_iL, lev_lev_lev]
end Formalism.FourierDecayAlt.P.B2x5
