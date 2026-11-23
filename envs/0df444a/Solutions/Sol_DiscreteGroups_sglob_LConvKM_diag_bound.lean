-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.diag_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:19.792882+00:00
-- url     : https://prove2.me/submissions/1eae35eb-b82c-4d48-bcbd-3593d5a8360e

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_InvF_smul
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_re_add_le
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_re_smul
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_mkForm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] DiscreteGroups.sglob.LConvKM.mkForm_apply

set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {G : Type*} [Group G] (ρ : Representation ℂ G M) (c : ℕ → ℝ) (xs : ℕ → M)
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (x : M) :
    ∃ R, ∀ F ∈ capSet ρ c xs, (F x x).re ≤ R := by
  have hx : x ∈ Submodule.span ℂ (Set.range xs) := by rw [hsp]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨1 / c i, fun F hF => ?_⟩
    have h1 := Finset.single_le_sum (f := fun j => c j * (F (xs j) (xs j)).re)
      (fun j _ => mul_nonneg (hc j).le (hF.1.1.2 (xs j))) (Finset.self_mem_range_succ i)
    have h2 := hF.2 (i + 1)
    rw [le_div_iff₀ (hc i)]
    linarith [mul_comm (F (xs i) (xs i)).re (c i)]
  | zero =>
    refine ⟨0, fun F hF => ?_⟩
    have h : mkForm F hF.1.1.1.1 0 0 = 0 := by simp only [map_zero, LinearMap.zero_apply]
    rw [mkForm_apply] at h
    rw [h, Complex.zero_re]
  | add x y _ _ hx hy =>
    obtain ⟨R₁, h₁⟩ := hx
    obtain ⟨R₂, h₂⟩ := hy
    refine ⟨2 * R₁ + 2 * R₂, fun F hF => ?_⟩
    have := re_add_le (mkForm F hF.1.1.1.1) hF.1.1.2 x y
    simp only [mkForm_apply] at this
    linarith [h₁ F hF, h₂ F hF]
  | smul a x _ hx =>
    obtain ⟨R, h⟩ := hx
    refine ⟨Complex.normSq a * R, fun F hF => ?_⟩
    have := re_smul (mkForm F hF.1.1.1.1) a x
    simp only [mkForm_apply] at this
    rw [this]
    exact mul_le_mul_of_nonneg_left (h F hF) (Complex.normSq_nonneg a)
end DiscreteGroups.sglob.LConvKM
