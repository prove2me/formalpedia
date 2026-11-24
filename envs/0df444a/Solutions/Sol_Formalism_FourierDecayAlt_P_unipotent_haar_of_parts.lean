-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unipotent_haar_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:37:42.246804+00:00
-- url     : https://prove2.me/submissions/42655201-e7ca-4285-aec1-3b1ae2206e41

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.AssembleHaarN := by
  intro hR hB k r
  induction r with
  | zero =>
    let o : Mt k 0 := (1 : Mat k 0)
    refine ⟨Measure.dirac o, ?_⟩
    rw [hB k]
    have hl : (lmulM (1 : Mat k 0)) = id := by funext x; simp [lmulM]; rfl
    have hr : (rmulF (1 : Mat k 0)) = id := by funext x; simp [rmulF]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show Measure.dirac o ({o}ᶜ : Set (Mt k 0)) = 0
      rw [Measure.dirac_apply' _ (MeasurableSet.singleton o).compl]
      simp
    · intro a ha
      rw [Set.mem_singleton_iff.mp ha, hl, Measure.map_id]
    · intro a ha
      rw [Set.mem_singleton_iff.mp ha, hr, Measure.map_id]
    · intro K _
      exact measure_lt_top _ _
    · exact IsProbabilityMeasure.ne_zero _
  | succ r' ih =>
    obtain ⟨μ', h'⟩ := ih
    rw [Nat.add_comm r' 1]
    exact ⟨_, hR k r' μ' h'⟩
end Formalism.FourierDecayAlt.P
