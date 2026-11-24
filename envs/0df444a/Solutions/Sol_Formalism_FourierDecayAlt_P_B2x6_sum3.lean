-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.sum3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:13:00.770014+00:00
-- url     : https://prove2.me/submissions/37d80ebb-e9bd-4a3e-b5c1-67ffff854388

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_val
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x6
theorem _root_.solution (f : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ p, f p = f (iF k r') + ∑ j, f (lv k r' j) + f (iL k r') := by
  have h : (2 * r' + k + 1) + 1 + 1 = 2 * (1 + r') + k + 1 := by omega
  rw [← (finCongr h).sum_comp, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have e0 : finCongr h 0 = iF k r' := Fin.ext (by rw [iF_val]; rfl)
  have e1 : finCongr h (Fin.succ (Fin.last _)) = iL k r' := Fin.ext (by rw [iL_val]; simp)
  have e2 : ∀ j : Fin (2 * r' + k + 1), finCongr h (Fin.succ (Fin.castSucc j)) = lv k r' j := by
    intro j; exact Fin.ext (by rw [lv_val]; simp)
  rw [e0, e1]
  simp only [e2]
  ring
end Formalism.FourierDecayAlt.P.B2x6
