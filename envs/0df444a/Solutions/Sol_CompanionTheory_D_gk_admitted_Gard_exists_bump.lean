-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.exists_bump
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:24.443735+00:00
-- url     : https://prove2.me/submissions/1fc1586f-37db-4249-9cdb-c92ebaba8a55

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_contDiff_hs
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_hs_conj
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_norm_le_of_hs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution {W : Set (Matrix (Fin n) (Fin n) ℂ)} (hW : W ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (S : Set (Matrix (Fin n) (Fin n) ℂ)), ContDiff ℝ ∞ f ∧ 0 ≤ f ∧ f 1 ≠ 0 ∧
      IsCompact S ∧ S ⊆ W ∧ (∀ y, f y ≠ 0 → y ∈ S) ∧
      ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ y, f (kᴴ * y * k) = f y := by
  obtain ⟨r, hr, hrW⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hW
  refine ⟨fun y => expNegInvGlue (r ^ 2 - hs (y - 1)), Metric.closedBall 1 r, ?_, fun y => expNegInvGlue.nonneg _,
    ?_, isCompact_closedBall _ _, hrW, fun y hy => ?_, fun k hk y => ?_⟩
  · exact expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_hs.comp (contDiff_id.sub contDiff_const)))
  · refine (expNegInvGlue.pos_of_pos ?_).ne'
    simp only [sub_self, hs, Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, sub_zero]
    positivity
  · rw [mem_closedBall_iff_norm]
    refine norm_le_of_hs hr.le ?_
    by_contra h
    exact hy (expNegInvGlue.zero_of_nonpos (by linarith))
  · have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
    have : kᴴ * y * k - 1 = kᴴ * (y - 1) * k := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    simp only [this, hs_conj hk]
end CompanionTheory.D.gk.admitted.Gard
