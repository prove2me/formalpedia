-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.lev_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:33:26.982945+00:00
-- url     : https://prove2.me/submissions/a6d0ceef-bf5e-4251-8c6a-339ca0e827e1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mid_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_n

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution (k r' : ℕ) : Continuous (ιLev k 1 r') := by
  refine continuous_matrix fun p q => ?_
  by_cases hp : mid k r' p
  · by_cases hq : mid k r' q
    · obtain ⟨s, rfl⟩ := (mid_iff k r' p).1 hp
      obtain ⟨t, rfl⟩ := (mid_iff k r' q).1 hq
      simp only [lev_mm]
      exact continuous_id.matrix_elem s t
    · simp only [lev_mn k r' _ p q hp hq]
      exact continuous_const
  · simp only [lev_n k r' _ p q hp]
    exact continuous_const
end Formalism.FourierDecayAlt.P.B2x2
