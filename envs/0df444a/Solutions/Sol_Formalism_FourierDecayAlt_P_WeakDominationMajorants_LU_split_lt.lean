-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU.split_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:14:12.040817+00:00
-- url     : https://prove2.me/submissions/d417fd98-c925-4b17-851f-2549e8eb4bf5

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
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
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
theorem _root_.solution (b : ℕ) (hb : b ≤ r) (f : Fin r → ℂ) :
    ∑ t, f t = ∑ l : Fin b, f (Fin.castLE hb l) + ∑ t, if b ≤ t.val then f t else 0 := by
  have h1 : ∀ t : Fin r, f t = (if t.val < b then f t else 0) + (if b ≤ t.val then f t else 0) := by
    intro t; by_cases h : t.val < b
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hb)
    (fun i _ j _ hij => Fin.castLE_injective hb hij)]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE hb)))]
  · refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 ht
    rw [if_pos (by simp)]
  · intro t _ ht
    rw [if_neg]
    intro h
    exact ht (Finset.mem_image.2 ⟨⟨t.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
