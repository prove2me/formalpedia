-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.hermitian_first_basis_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:22:44.69395+00:00
-- url     : https://prove2.me/submissions/e398b115-b1ed-4114-aa3e-322ef371540b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_bvec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_Hpk_zero_row
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_herm_bvec


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x4
theorem _root_.solution (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (e0 k r') = u (lastI k r') := by
  rw [← herm_sum]
  rw [Finset.sum_eq_single (lastI k r')]
  · rw [e0, herm_bvec, Hpk_zero_row, if_pos (show (lastI k r').val = 2 * (1 + r') + k from rfl), one_mul]
  · intro j _ hj
    have : j.val ≠ 2 * (1 + r') + k := fun h => hj (Fin.ext h)
    rw [e0, herm_bvec, Hpk_zero_row, if_neg this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.B2x4
