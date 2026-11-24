-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.exists_isBump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:36:14.015727+00:00
-- url     : https://prove2.me/submissions/bbf372d0-33c0-4ab5-a97d-13ed2ea9e15a

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_exists_bump
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {hG : IsMatGroup G}
namespace CompanionTheory.D.gk.Poul
theorem _root_.solution (hG : IsMatGroup G) (θ : Mat n →L[ℝ] Mat n) (hθ : ∀ x ∈ G, θ x = x⁻¹) {V : Set (MG G hG)}
    (hV : V ∈ 𝓝 (1 : MG G hG)) : ∃ φ, IsBump G φ ∧ ∀ x : MG G hG, φ x.mat ≠ 0 → x ∈ V := by
  rw [MG.isClosedEmbedding_mat.isInducing.nhds_eq_comap, mem_comap] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  have hD : {y : Mat n | y.det ≠ 0} ∈ 𝓝 (1 : Mat n) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, hf0, hf1, hS, hSW, hfS, -⟩ := exists_bump (inter_mem hW hD)
  refine ⟨fun y => f y * f (θ y), ⟨hf.mul (hf.comp θ.contDiff), fun y => mul_nonneg (hf0 _) (hf0 _), ?_,
    fun x hx => ?_, S, hS, fun B hB => (hSW hB).2, fun y hy => hfS _ (left_ne_zero_of_mul hy)⟩,
    fun x hx => hWV (hSW (hfS _ (left_ne_zero_of_mul hx))).1⟩
  · show f 1 * f (θ 1) ≠ 0
    rw [hθ 1 hG.2.1, inv_one]
    exact mul_ne_zero hf1 hf1
  · show f x⁻¹ * f (θ x⁻¹) = f x * f (θ x)
    have hu : IsUnit x.det := Matrix.isUnit_det_of_right_inverse (hG.2.2.2 x hx).2
    rw [hθ _ (hG.2.2.2 x hx).1, hθ x hx, Matrix.nonsing_inv_nonsing_inv x hu, mul_comm]
end CompanionTheory.D.gk.Poul
