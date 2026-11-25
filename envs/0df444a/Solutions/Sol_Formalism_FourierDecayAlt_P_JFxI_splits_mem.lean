-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxI.splits_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:04:18.452311+00:00
-- url     : https://prove2.me/submissions/ce596121-9ba7-453d-8164-11818e5bf0c0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
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
namespace Formalism.FourierDecayAlt.P.JFxI
theorem _root_.solution {α : Type*} : ∀ (w : List α), ∀ uv ∈ splits w,
    (∀ X ∈ uv.1, X ∈ w) ∧ (∀ X ∈ uv.2, X ∈ w) ∧ uv.2.length ≤ w.length
  | [], uv, h => by simp [splits] at h; subst h; simp
  | X :: w, uv, h => by
    simp only [splits, List.mem_append, List.mem_map] at h
    rcases h with ⟨uv', h', rfl⟩ | ⟨uv', h', rfl⟩
    · obtain ⟨a, b, c⟩ := solution w uv' h'
      refine ⟨?_, fun Y hY => List.mem_cons_of_mem _ (b Y hY), by simp; omega⟩
      intro Y hY
      rcases List.mem_cons.1 hY with rfl | hY
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (a Y hY)
    · obtain ⟨a, b, c⟩ := solution w uv' h'
      refine ⟨fun Y hY => List.mem_cons_of_mem _ (a Y hY), ?_, by simp; omega⟩
      intro Y hY
      rcases List.mem_cons.1 hY with rfl | hY
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (b Y hY)
end Formalism.FourierDecayAlt.P.JFxI
