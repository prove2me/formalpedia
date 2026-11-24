-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.extreme_exists_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:17.963061+00:00
-- url     : https://prove2.me/submissions/607e0e54-12c0-42ac-954d-d15a457acd5c

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_InvF_smul
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_continuous_eval
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_comb_apply
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_mkForm_apply
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_invF_mkForm
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_ev_mem
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_convex_capSet
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_isCompact_capSet
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_ray
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
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution {G : Type*} [Group G] (ρ : Representation ℂ G M)
    (hspan : ∃ s : Set M, s.Countable ∧ Submodule.span ℂ s = ⊤)
    (B₀ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (h₀ : InvF ρ B₀) (f : M) (hf : B₀ f f ≠ 0) :
    ∃ B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, (InvF ρ B ∧ ∀ B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, InvF ρ B' → InvF ρ (B - B') →
      ∃ c : ℂ, ∀ x y, B' x y = c * B x y) ∧ B f f ≠ 0 := by
  obtain ⟨s, hsc, hss⟩ := hspan
  obtain ⟨xs, hxs⟩ := (hsc.insert 0).exists_eq_range (Set.insert_nonempty 0 s)
  have hsp : Submodule.span ℂ (Set.range xs) = ⊤ := by rw [← hxs, Submodule.span_insert_zero, hss]
  obtain ⟨c, hc_def⟩ : ∃ c : ℕ → ℝ, c = fun i => (1 / 2 : ℝ) ^ i / (1 + (B₀ (xs i) (xs i)).re) := ⟨_, rfl⟩
  have hc : ∀ i, 0 < c i := fun i => by
    simp only [hc_def]
    exact div_pos (by positivity) (by linarith [h₀.2.1 (xs i)])
  have hhalf : InvF ρ (((1 / 2 : ℝ) : ℂ) • B₀) := h₀.smul (by norm_num)
  have hmem₀ : ev (((1 / 2 : ℝ) : ℂ) • B₀) ∈ capSet ρ c xs := by
    refine ev_mem ρ c xs hhalf fun n => ?_
    show ∑ i ∈ Finset.range n, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re ≤ 1
    have hterm : ∀ i, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re ≤ (1 / 2) * (1 / 2 : ℝ) ^ i := by
      intro i
      have hr := h₀.2.1 (xs i)
      have hp : (0 : ℝ) < (1 / 2) ^ i := by positivity
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul, hc_def]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc ∑ i ∈ Finset.range n, c i * ((((1 / 2 : ℝ) : ℂ) • B₀) (xs i) (xs i)).re
        ≤ ∑ i ∈ Finset.range n, (1 / 2) * (1 / 2 : ℝ) ^ i := Finset.sum_le_sum fun i _ => hterm i
      _ = (1 / 2) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
      _ ≤ 1 := by linarith [sum_geometric_two_le n]
  obtain ⟨F, hFe, hFf⟩ : ∃ F ∈ (capSet ρ c xs).extremePoints ℝ, F f f ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have hZ : IsClosed {F : M → M → ℂ | F f f = 0} := isClosed_eq (continuous_eval f f) continuous_const
    have hZc : Convex ℝ {F : M → M → ℂ | F f f = 0} := by
      intro F hF G hG a b _ _ _
      have hF' : F f f = 0 := hF
      have hG' : G f f = 0 := hG
      show (a • F + b • G) f f = 0
      rw [comb_apply, hF', hG', mul_zero, mul_zero, add_zero]
    have hsub : capSet ρ c xs ⊆ {F | F f f = 0} := by
      rw [← closure_convexHull_extremePoints (isCompact_capSet ρ c xs hsp hc) (convex_capSet ρ c xs)]
      exact closure_minimal (convexHull_min (fun F hF => hcon F hF) hZc) hZ
    have h : ((1 / 2 : ℝ) : ℂ) * B₀ f f = 0 := hsub hmem₀
    apply hf
    simpa using h
  have hFm := (mem_extremePoints.mp hFe).1
  exact ⟨mkForm F hFm.1.1.1.1, ⟨invF_mkForm ρ c xs hFm, fun B' h1 h2 => ray ρ c xs hsp hc (mkForm F hFm.1.1.1.1) hFe B' h1 h2⟩, hFf⟩
end DiscreteGroups.sglob.LConvKM
