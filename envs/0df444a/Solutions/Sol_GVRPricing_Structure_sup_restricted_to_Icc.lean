-- Prove2me | solution 1 for GVRPricing.Structure.sup_restricted_to_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:16:13.615028+00:00
-- url     : https://prove2.me/submissions/dc94d896-7fea-4461-91a4-4b92b711b119

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model
import Definitions.Def_GVRPricing_Structure_IsHJBSolution

set_option autoImplicit false

open GVRPricing.Structure in
theorem solution (M : Model) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    BddAbove (hamObjective M Δ '' M.Λ) ∧
    sSup (hamObjective M Δ '' M.Λ) = sSup (hamObjective M Δ '' Set.Icc 0 M.lamStar) ∧
    ∃ x ∈ Set.Icc 0 M.lamStar, IsMaxOn (hamObjective M Δ) M.Λ x := by
  have hls : M.lamStar ∈ M.Λ := M.lamStar_isLeast.1.1
  have hmax : ∀ y ∈ M.Λ, revRate M.p y ≤ revRate M.p M.lamStar := M.lamStar_isLeast.1.2
  have h0 : (0:ℝ) ≤ M.lamStar := M.subset_nonneg hls
  have hsub : Set.Icc 0 M.lamStar ⊆ M.Λ := M.ordConnected.out M.zero_mem hls
  have hcont : ContinuousOn (hamObjective M Δ) (Set.Icc 0 M.lamStar) := by
    have hr : ContinuousOn (revRate M.p) (Set.Icc 0 M.lamStar) := M.r_continuousOn.mono hsub
    unfold hamObjective Model.r
    exact hr.sub (continuousOn_id.mul continuousOn_const)
  obtain ⟨x, hx, hxmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 h0) hcont
  have hM : IsMaxOn (hamObjective M Δ) M.Λ x := by
    intro y hy
    rcases le_or_gt y M.lamStar with h | h
    · exact hxmax ⟨M.subset_nonneg hy, h⟩
    · have h1 : hamObjective M Δ y ≤ hamObjective M Δ M.lamStar := by
        unfold hamObjective Model.r
        have h2 := hmax y hy
        have h3 := mul_le_mul_of_nonneg_right h.le hΔ
        linarith
      exact h1.trans (hxmax ⟨h0, le_rfl⟩)
  have hG1 : IsGreatest (hamObjective M Δ '' M.Λ) (hamObjective M Δ x) :=
    ⟨Set.mem_image_of_mem _ (hsub hx), by rintro _ ⟨y, hy, rfl⟩; exact hM hy⟩
  have hG2 : IsGreatest (hamObjective M Δ '' Set.Icc 0 M.lamStar) (hamObjective M Δ x) :=
    ⟨Set.mem_image_of_mem _ hx, by rintro _ ⟨y, hy, rfl⟩; exact hxmax hy⟩
  exact ⟨hG1.bddAbove, hG1.csSup_eq.trans hG2.csSup_eq.symm, x, hx, hM⟩
