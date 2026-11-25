-- Prove2me | solution 1 for CompanionTheory.D.gk.HwAlg.eq_smul_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:13:27.482223+00:00
-- url     : https://prove2.me/submissions/a02ec3ee-33e3-4438-b6a5-d826942d0a3d

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_diag_word
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_hgt_wt_re
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_hOp_of_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons

set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Qr
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.HwAlg
variable {U : Type} [AddCommGroup U] [Module ℂ U] {n : ℕ}
variable {F : Fin n → Fin n → Module.End ℂ U} {ν : Fin n → ℂ} {w : U}
namespace CompanionTheory.D.gk.HwAlg
theorem _root_.solution (hF : GlRel F) (hw : IsHW F ν w) {x : U} (hx : x ∈ lowSpan F w)
    (hxν : ∀ c, F c c x = ν c • x) : ∃ t : ℂ, x = t • w := by
  set S1 : Set U := {y | ∃ l, Lower l ∧ l ≠ [] ∧ y = word F l w} with hS1
  have hset : {y | ∃ l, Lower l ∧ y = word F l w} = insert w S1 := by
    ext y; constructor
    · rintro ⟨l, hl, rfl⟩
      rcases l with _ | ⟨p, l⟩
      · left; simp
      · right; exact ⟨p :: l, hl, by simp, rfl⟩
    · rintro (rfl | ⟨l, hl, -, rfl⟩)
      · exact ⟨[], by simp [Lower], by simp⟩
      · exact ⟨l, hl, rfl⟩
  rw [lowSpan, hset, Submodule.mem_span_insert] at hx
  obtain ⟨t, y, hy, rfl⟩ := hx
  refine ⟨t, ?_⟩
  suffices y = 0 by rw [this, add_zero]

  have hy1 : y ∈ ⨆ (μ : ℂ) (_ : μ ≠ hgt ν), (hOp F).eigenspace μ := by
    refine (Submodule.span_le.2 ?_) hy
    rintro z ⟨l, hl, hne, rfl⟩
    have hre := hgt_wt_re ν l hl
    have hlen : (1 : ℝ) ≤ l.length := by
      rcases l with _ | ⟨p, l⟩
      · exact absurd rfl hne
      · simp
    have hne' : hgt (wt ν l) ≠ hgt ν := by
      intro h; rw [h] at hre; linarith
    refine Submodule.mem_iSup_of_mem (hgt (wt ν l)) (Submodule.mem_iSup_of_mem hne' ?_)
    rw [Module.End.mem_eigenspace_iff]
    exact hOp_of_diag (diag_word hF hw l)

  have hy2 : y ∈ (hOp F).eigenspace (hgt ν) := by
    rw [Module.End.mem_eigenspace_iff]
    have h1 : hOp F (t • w + y) = hgt ν • (t • w + y) := hOp_of_diag hxν
    have h2 : hOp F w = hgt ν • w := hOp_of_diag hw.1
    rw [map_add, map_smul, h2, smul_add, smul_comm] at h1
    exact add_left_cancel h1
  have hdisj := (Module.End.eigenspaces_iSupIndep (hOp F)) (hgt ν)
  exact (Submodule.disjoint_def.1 hdisj) y hy2 hy1
end CompanionTheory.D.gk.HwAlg
