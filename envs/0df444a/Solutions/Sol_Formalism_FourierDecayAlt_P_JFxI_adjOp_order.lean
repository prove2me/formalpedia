-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxI.adjOp_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:32.885013+00:00
-- url     : https://prove2.me/submissions/b19f4222-4933-4e03-a46b-885679adc585

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxI_splits_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxI_splits_full
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxI_lieOr_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxI_lieOr_len
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxI_foldr_max_le_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
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
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.JFxI
theorem _root_.solution (Θ : DiffOp k r Wp Wq) : opOrder (adjOp Θ) = opOrder Θ := by
  have key : ∀ (L : List ℕ) (x : ℕ), x ∈ L → x ≤ L.foldr max 0 :=
    fun L x hx => (foldr_max_le_iff L _).1 le_rfl x hx
  unfold opOrder
  apply le_antisymm
  · rw [foldr_max_le_iff]
    intro x hx
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hx
    unfold adjOp at hT'
    obtain ⟨T, hT, hT''⟩ := List.mem_flatMap.1 hT'
    obtain ⟨uv, huv, rfl⟩ := List.mem_map.1 hT''
    calc (adjTerm T uv).word.length = (lieOr uv.2).length := rfl
      _ ≤ uv.2.length := lieOr_len _
      _ ≤ T.word.reverse.length := (splits_mem _ uv huv).2.2
      _ = T.word.length := by simp
      _ ≤ _ := key _ _ (List.mem_map.2 ⟨T, hT, rfl⟩)
  · rw [foldr_max_le_iff]
    intro x hx
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
    have hlie : ∀ X ∈ T.word.reverse, inLie k r X := fun X hX => T.word_lie X (List.mem_reverse.1 hX)
    have hmem : adjTerm T ([], T.word.reverse) ∈ adjOp Θ := by
      unfold adjOp
      exact List.mem_flatMap.2 ⟨T, hT, List.mem_map.2 ⟨_, splits_full _, rfl⟩⟩
    calc T.word.length = (adjTerm T ([], T.word.reverse)).word.length := by
          show T.word.length = (lieOr T.word.reverse).length
          rw [lieOr_eq hlie, List.length_reverse]
      _ ≤ _ := key _ _ (List.mem_map.2 ⟨_, hmem, rfl⟩)
end Formalism.FourierDecayAlt.P.JFxI
