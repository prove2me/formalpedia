-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.H_lev_iL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:01:33.018874+00:00
-- url     : https://prove2.me/submissions/562d8126-1cc4-4ad0-93b3-daf15aaa6c55

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
theorem _root_.solution (k r' : ℕ) (i : Fin (2 * r' + k + 1)) : Hpk k (1 + r') (levPos k 1 r' i) (iL k r') = 0 := by
  have hi := i.isLt
  simp only [Hpk, iL_val, lev_val, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | (simp_all [Fin.ext_iff] <;> omega)
end Formalism.FourierDecayAlt.P.B2x5
