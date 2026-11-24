-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.lev_ne_iL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:03:15.316291+00:00
-- url     : https://prove2.me/submissions/42a58089-14ca-4489-a4bf-881c245b1cf8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_val

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
theorem _root_.solution (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : levPos k 1 r' j ≠ iL k r' := by
  intro h
  have := congrArg Fin.val h
  rw [lev_val, iL_val] at this
  have := j.isLt
  omega
end Formalism.FourierDecayAlt.P.B2x5
