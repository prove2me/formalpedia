-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.rho_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:36:32.396044+00:00
-- url     : https://prove2.me/submissions/1a175b38-d8fb-48ad-bd34-82a146de6b97

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_cases3
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mF
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x6
theorem _root_.solution : Continuous (rho (k := k) (r' := r')) := by
  apply continuous_pi; intro p
  apply continuous_pi; intro q
  show Continuous fun x : Mt k (1 + r') => ιLev k 1 r' (blk (Matrix.of x)) p q
  rcases cases3 p with rfl | rfl | ⟨i, rfl⟩
  · simp only [lev_F]; exact continuous_const
  · simp only [lev_L]; exact continuous_const
  · rcases cases3 q with rfl | rfl | ⟨j, rfl⟩
    · simp only [lev_mF]; exact continuous_const
    · simp only [lev_mL]; exact continuous_const
    · simp only [lev_mm]
      show Continuous fun x : Mt k (1 + r') => x (lv k r' i) (lv k r' j)
      exact (continuous_apply _).comp (continuous_apply _)
end Formalism.FourierDecayAlt.P.B2x6
