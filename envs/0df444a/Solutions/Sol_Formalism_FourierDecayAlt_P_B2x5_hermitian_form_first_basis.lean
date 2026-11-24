-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.hermitian_form_first_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:01:31.862322+00:00
-- url     : https://prove2.me/submissions/65c1cd9d-b917-4e0f-9690-1f521ef6b753

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_first_index_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val

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
theorem _root_.solution (k r' : ℕ) (q : Fin (2 * (1 + r') + k + 1)) :
    Hpk k (1 + r') (i0 k r') q = if q = iL k r' then 1 else 0 := by
  have hq := q.isLt
  simp only [Hpk, first_index_val, iL_val, Fin.ext_iff]
  split_ifs <;> first | rfl | omega
end Formalism.FourierDecayAlt.P.B2x5
