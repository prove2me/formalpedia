-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.lev_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:16:27.92067+00:00
-- url     : https://prove2.me/submissions/9b1fe583-d1b5-4e94-8646-10e8f3c5458a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_ne_iF
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_inj
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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_uh
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff

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
theorem _root_.solution {g : Mat k r'} (hg : g ∈ Nset k r') : ιLev k 1 r' g ∈ Nset k (1 + r') := by
  rw [WeylGroupFacts.nset_iff] at hg ⊢
  refine ⟨lev_uh hg.1, ?_⟩
  intro i j hj hi
  rcases cases3 i with rfl | rfl | ⟨i', rfl⟩
  · exact lev_F g j
  · exact lev_L g j
  · rcases cases3 j with rfl | rfl | ⟨j', rfl⟩
    · rw [lev_mF, if_neg (lv_ne_iF i')]
    · rw [iL_val] at hj; omega
    · rw [lv_val] at hj hi
      rw [lv_val] at hi
      rw [lev_mm, hg.2 i' j' (by omega) (by omega)]
      simp only [lv_inj]
end Formalism.FourierDecayAlt.P.B2x6
