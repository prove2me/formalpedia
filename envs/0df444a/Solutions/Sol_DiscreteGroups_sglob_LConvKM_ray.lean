-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.ray
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:44.897401+00:00
-- url     : https://prove2.me/submissions/d14a5dce-18b5-43ac-a5c1-e3dfa2063281

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_InvF_smul
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_eq_zero_of_re
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_comb_apply
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_mkForm_apply
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_ev_mem
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
theorem _root_.solution (hsp : Submodule.span ℂ (Set.range xs) = ⊤) (hc : ∀ i, 0 < c i) (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (hB : ev B ∈ (capSet ρ c xs).extremePoints ℝ) (B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (h1 : InvF ρ B') (h2 : InvF ρ (B - B')) : ∃ k : ℂ, ∀ x y, B' x y = k * B x y := by
  obtain ⟨hBm, hBx⟩ := mem_extremePoints.mp hB
  have hcapB : ∀ n, ∑ i ∈ Finset.range n, c i * (B (xs i) (xs i)).re ≤ 1 := hBm.2
  have hsplit : ∀ i, c i * (B (xs i) (xs i)).re
      = c i * (B' (xs i) (xs i)).re + c i * ((B - B') (xs i) (xs i)).re := by
    intro i; rw [LinearMap.sub_apply, LinearMap.sub_apply, Complex.sub_re]; ring
  have h0' : ∀ i, 0 ≤ c i * (B' (xs i) (xs i)).re := fun i => mul_nonneg (hc i).le (h1.2.1 _)
  have h0'' : ∀ i, 0 ≤ c i * ((B - B') (xs i) (xs i)).re := fun i => mul_nonneg (hc i).le (h2.2.1 _)
  have hb' : ∀ n, ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re ≤ 1 := fun n => by
    have := hcapB n
    simp only [hsplit, Finset.sum_add_distrib] at this
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) => h0'' i]
  have hb'' : ∀ n, ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re ≤ 1 := fun n => by
    have := hcapB n
    simp only [hsplit, Finset.sum_add_distrib] at this
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range n) => h0' i]
  have hs' := summable_of_sum_range_le h0' hb'
  have hs'' := summable_of_sum_range_le h0'' hb''
  have hP : ∑' i, c i * (B' (xs i) (xs i)).re + ∑' i, c i * ((B - B') (xs i) (xs i)).re ≤ 1 := by
    rw [← hs'.tsum_add hs'']
    refine (hs'.add hs'').tsum_le_of_sum_range_le fun n => ?_
    have := hcapB n
    simp only [hsplit] at this
    exact this
  have hle' : ∀ n, ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re
      ≤ ∑' i, c i * (B' (xs i) (xs i)).re := fun n => hs'.sum_le_tsum _ (fun i _ => h0' i)
  have hle'' : ∀ n, ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re
      ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re := fun n => hs''.sum_le_tsum _ (fun i _ => h0'' i)
  have hi' : ∀ i, c i * (B' (xs i) (xs i)).re ≤ ∑' i, c i * (B' (xs i) (xs i)).re :=
    fun i => hs'.le_tsum i (fun j _ => h0' j)
  have hi'' : ∀ i, c i * ((B - B') (xs i) (xs i)).re ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re :=
    fun i => hs''.le_tsum i (fun j _ => h0'' j)
  have hnn' : 0 ≤ ∑' i, c i * (B' (xs i) (xs i)).re := tsum_nonneg h0'
  have hnn'' : 0 ≤ ∑' i, c i * ((B - B') (xs i) (xs i)).re := tsum_nonneg h0''
  generalize ∑' i, c i * (B' (xs i) (xs i)).re = p' at hP hle' hi' hnn'
  generalize ∑' i, c i * ((B - B') (xs i) (xs i)).re = p'' at hP hle'' hi'' hnn''
  have zero_of : ∀ B₁ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, InvF ρ B₁ → (∀ i, c i * (B₁ (xs i) (xs i)).re ≤ 0) →
      ∀ x y, B₁ x y = 0 := by
    intro B₁ hB₁ hle x y
    refine eq_zero_of_re B₁ hB₁.1 hB₁.2.1 xs hsp (fun i => ?_) x y
    have h0 := mul_nonneg (hc i).le (hB₁.2.1 (xs i))
    have := le_antisymm (hle i) h0
    exact (mul_eq_zero.mp this).resolve_left (hc i).ne'
  rcases hnn'.lt_or_eq with hp' | hp'
  swap
  · refine ⟨0, fun x y => ?_⟩
    rw [zero_of B' h1 (fun i => (hi' i).trans hp'.ge) x y, zero_mul]
  rcases hnn''.lt_or_eq with hp'' | hp''
  swap
  · refine ⟨1, fun x y => ?_⟩
    have := zero_of (B - B') h2 (fun i => (hi'' i).trans hp''.ge) x y
    rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_eq_zero] at this
    rw [this, one_mul]
  have hPpos : 0 < p' + p'' := by linarith
  have hne' := hp'.ne'
  have hne'' := hp''.ne'
  have hPne := hPpos.ne'
  have hr' : (0 : ℝ) ≤ (p' + p'') / p' := div_nonneg hPpos.le hp'.le
  have hr'' : (0 : ℝ) ≤ (p' + p'') / p'' := div_nonneg hPpos.le hp''.le
  have hF1 : ev ((((p' + p'') / p' : ℝ) : ℂ) • B') ∈ capSet ρ c xs := by
    refine ev_mem ρ c xs (h1.smul hr') fun n => ?_
    show ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p' : ℝ) : ℂ) • B') (xs i) (xs i)).re ≤ 1
    have e : ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p' : ℝ) : ℂ) • B') (xs i) (xs i)).re
        = (p' + p'') / p' * ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      ring
    rw [e]
    calc (p' + p'') / p' * ∑ i ∈ Finset.range n, c i * (B' (xs i) (xs i)).re
        ≤ (p' + p'') / p' * p' := mul_le_mul_of_nonneg_left (hle' n) hr'
      _ = p' + p'' := by field_simp
      _ ≤ 1 := hP
  have hF2 : ev ((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) ∈ capSet ρ c xs := by
    refine ev_mem ρ c xs (h2.smul hr'') fun n => ?_
    show ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) (xs i) (xs i)).re ≤ 1
    have e : ∑ i ∈ Finset.range n, c i * (((((p' + p'') / p'' : ℝ) : ℂ) • (B - B')) (xs i) (xs i)).re
        = (p' + p'') / p'' * ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      ring
    rw [e]
    calc (p' + p'') / p'' * ∑ i ∈ Finset.range n, c i * ((B - B') (xs i) (xs i)).re
        ≤ (p' + p'') / p'' * p'' := mul_le_mul_of_nonneg_left (hle'' n) hr''
      _ = p' + p'' := by field_simp
      _ ≤ 1 := hP
  have k1r : p' / (p' + p'') * ((p' + p'') / p') = 1 := by field_simp
  have k2r : p'' / (p' + p'') * ((p' + p'') / p'') = 1 := by field_simp
  have k1 : ((p' / (p' + p'') : ℝ) : ℂ) * (((p' + p'') / p' : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, k1r, Complex.ofReal_one]
  have k2 : ((p'' / (p' + p'') : ℝ) : ℂ) * (((p' + p'') / p'' : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, k2r, Complex.ofReal_one]
  have hseg : ev B ∈ openSegment ℝ (ev ((((p' + p'') / p' : ℝ) : ℂ) • B'))
      (ev ((((p' + p'') / p'' : ℝ) : ℂ) • (B - B'))) := by
    refine ⟨p' / (p' + p''), p'' / (p' + p''), div_pos hp' hPpos, div_pos hp'' hPpos, by field_simp, ?_⟩
    funext x y
    rw [comb_apply]
    simp only [ev, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
    linear_combination (B' x y) * k1 + (B x y - B' x y) * k2
  have hx := hBx _ hF1 _ hF2 hseg
  refine ⟨((p' / (p' + p'') : ℝ) : ℂ), fun x y => ?_⟩
  have e := congrFun (congrFun hx.1 x) y
  simp only [ev, LinearMap.smul_apply, smul_eq_mul] at e
  rw [← e]
  linear_combination (-(B' x y)) * k1
end DiscreteGroups.sglob.LConvKM
