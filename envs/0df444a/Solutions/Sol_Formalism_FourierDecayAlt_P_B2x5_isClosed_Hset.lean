-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.isClosed_Hset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:00:49.283298+00:00
-- url     : https://prove2.me/submissions/6670a219-6ff4-4631-aeee-1d1d196f653c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_heis0
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_Hset_eq

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
theorem _root_.solution (k r' : ℕ) : IsClosed (Hset k r') := by
  rw [Hset_eq]
  exact isClosed_eq ((continuous_heis0 k r').comp (continuous_coord k r')) continuous_id
end Formalism.FourierDecayAlt.P.B2x5
