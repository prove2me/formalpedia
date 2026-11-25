-- Prove2me | solution 1 for FiniteEnergyPlane.eventually_exists_eq_of_fderiv_eq_reeb
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T12:49:03.301787+00:00
-- url     : https://prove2.me/submissions/80affa8d-a14e-45a5-b7ef-09c786661996

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_exists_equiv_hasStrictFDerivAt_exp_smul_of_injective



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma pfo_ne_zero {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) : x ≠ 0 := by
  rintro rfl
  have := hH.2.2 0 hx
  simp at this

lemma pfo_proj_mem {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n} (hy : y ≠ 0) :
    H (proj H y) = 1 := proj_mem_energySurface H hH y hy

lemma pfo_proj_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) {r : ℝ} (hr : 0 < r) : proj H (r • x) = x :=
  proj_smul_eq_of_mem_energySurface H hH x hx r hr

lemma pfo_proj_self {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V n}
    (hx : H x = 1) : proj H x = x := by
  simpa using pfo_proj_smul hH hx one_pos

lemma pfo_eq_smul {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V n}
    (hy : y ≠ 0) : ∃ r : ℝ, y = Real.exp r • proj H y := by
  obtain ⟨s, hs, hsy⟩ := (hH.2.1 _ hy).exists
  refine ⟨-Real.log s, ?_⟩
  have h := pfo_proj_smul hH hsy (inv_pos.2 hs)
  rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at h
  rw [h, Real.exp_neg, Real.exp_log hs, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

lemma pfo_smul_eq {n : ℕ} {H : V n → ℝ} (hH : IsStrictlyStarShapedLevel H) {x q : V n} {r : ℝ}
    (hx : H x = 1) (hq : H q = 1) (h : Real.exp r • x = q) : x = q := by
  rw [← pfo_proj_smul hH hx (Real.exp_pos r), h, pfo_proj_self hH hq]

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem eventually_exists_eq_of_fderiv_eq_reeb_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (F : ℝ × ℂ → V 1) (p : ℝ × ℂ) (hF : ContDiffAt ℝ 1 F p)
    (hFS : ∀ᶠ q in 𝓝 p, F q ∈ energySurface H) (hinj : Function.Injective (fderiv ℝ F p))
    (c : ℝ) (hc : 0 < c) (v : ℂ) (hcv : fderiv ℝ F p (c, v) = reeb H (F p))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (b : ℝ) (hb : y b = F p)
    (N : Set (ℝ × ℂ)) (hN : N ∈ 𝓝 p) :
    (∀ᶠ s in 𝓝[>] b, ∃ q ∈ N, p.1 < q.1 ∧ F q = y s) ∧
      ∀ᶠ s in 𝓝[<] b, ∃ q ∈ N, q.1 < p.1 ∧ F q = y s := by
  obtain ⟨-, L, hL, hs⟩ := exists_equiv_hasStrictFDerivAt_exp_smul_of_injective (by simp [Module.finrank_prod]) H hH F p hF hFS hinj
  set G : ℝ × ℝ × ℂ → V 1 := fun q => Real.exp q.1 • F q.2 with hGdef
  have hGp : G ((0 : ℝ), p) = y b := by simp [hGdef, hb]
  let g := hs.localInverse G L _
  have hg : HasStrictFDerivAt g (L.symm : V 1 →L[ℝ] ℝ × ℝ × ℂ) (y b) := by
    rw [← hGp]; exact hs.to_localInverse
  have hgb : g (y b) = ((0 : ℝ), p) := by rw [← hGp]; exact hs.localInverse_apply_image
  have hGg : ∀ᶠ q in 𝓝 (y b), G (g q) = q := by
    rw [← hGp]; exact hs.eventually_right_inverse
  have hyc : ContinuousAt y b := (hy.2 b).continuousAt
  have hgc : Tendsto (fun s => g (y s)) (𝓝 b) (𝓝 ((0 : ℝ), p)) := by
    have := hg.continuousAt.tendsto.comp hyc.tendsto
    rwa [hgb] at this
  have hd : HasDerivAt (fun s => g (y s)) ((0 : ℝ), (c, v)) b := by
    have h1 := hg.hasFDerivAt.comp_hasDerivAt b (hy.2 b)
    have h2 : (L.symm : V 1 →L[ℝ] ℝ × ℝ × ℂ) (reeb H (y b)) = ((0 : ℝ), (c, v)) := by
      show L.symm _ = _
      rw [ContinuousLinearEquiv.symm_apply_eq, hL]
      simp [hcv, hb]
    rw [h2] at h1
    exact h1
  have hd1 : HasDerivAt (fun s => (g (y s)).2.1) c b :=
    (((ContinuousLinearMap.fst ℝ ℝ ℂ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))).hasFDerivAt).comp_hasDerivAt b hd
  have hb1 : (g (y b)).2.1 = p.1 := by rw [hgb]
  have hev : ∀ᶠ s in 𝓝 b, (g (y s)).2 ∈ N ∧ F (g (y s)).2 = y s := by
    have h1 : ∀ᶠ q in 𝓝 ((0 : ℝ), p), q.2 ∈ N ∧ F q.2 ∈ energySurface H :=
      (continuous_snd.tendsto ((0 : ℝ), p)).eventually (Filter.Eventually.and hN hFS)
    filter_upwards [hgc.eventually h1, hyc.eventually hGg] with s h2 h3
    exact ⟨h2.1, pfo_smul_eq hH h2.2 (hy.1 s) h3⟩
  have hsl := (hasDerivAt_iff_tendsto_slope.1 hd1).eventually (lt_mem_nhds hc)
  rw [eventually_nhdsWithin_iff] at hsl
  constructor
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [hev, hsl] with s h1 h2 hsb
    have hsb : b < s := hsb
    refine ⟨_, h1.1, ?_, h1.2⟩
    have := h2 hsb.ne'
    rw [slope_def_field, hb1] at this
    have h3 : 0 < s - b := sub_pos.2 hsb
    have := (div_pos_iff_of_pos_right h3).1 this
    linarith
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [hev, hsl] with s h1 h2 hsb
    have hsb : s < b := hsb
    refine ⟨_, h1.1, ?_, h1.2⟩
    have := h2 hsb.ne
    rw [slope_def_field, hb1] at this
    have h3 : s - b < 0 := sub_neg.2 hsb
    rcases div_pos_iff.1 this with h | h <;> linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (F : ℝ × ℂ → V 1) (p : ℝ × ℂ) (hF : ContDiffAt ℝ 1 F p)
    (hFS : ∀ᶠ q in 𝓝 p, F q ∈ energySurface H) (hinj : Function.Injective (fderiv ℝ F p))
    (c : ℝ) (hc : 0 < c) (v : ℂ) (hcv : fderiv ℝ F p (c, v) = reeb H (F p))
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (b : ℝ) (hb : y b = F p)
    (N : Set (ℝ × ℂ)) (hN : N ∈ 𝓝 p) :
    (∀ᶠ s in 𝓝[>] b, ∃ q ∈ N, p.1 < q.1 ∧ F q = y s) ∧
      ∀ᶠ s in 𝓝[<] b, ∃ q ∈ N, q.1 < p.1 ∧ F q = y s :=
  eventually_exists_eq_of_fderiv_eq_reeb_aux H hH F p hF hFS hinj c hc v hcv y hy b hb N hN
