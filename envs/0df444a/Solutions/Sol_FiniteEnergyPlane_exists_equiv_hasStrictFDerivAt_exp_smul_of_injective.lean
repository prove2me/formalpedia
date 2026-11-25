-- Prove2me | solution 1 for FiniteEnergyPlane.exists_equiv_hasStrictFDerivAt_exp_smul_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T12:25:01.299169+00:00
-- url     : https://prove2.me/submissions/ef426aed-f5ed-4384-9ee3-58cda45ea805

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_proj_mem_energySurface
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface



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

theorem exists_equiv_hasStrictFDerivAt_exp_smul_of_injective_aux {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2 * n + 1) (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (F : E → V n) (p : E) (hF : ContDiffAt ℝ 1 F p)
    (hFS : ∀ᶠ q in 𝓝 p, F q ∈ energySurface H) (hinj : Function.Injective (fderiv ℝ F p)) :
    (∀ v, fderiv ℝ H (F p) (fderiv ℝ F p v) = 0) ∧
    ∃ L : (ℝ × E) ≃L[ℝ] V n, (∀ q, L q = q.1 • F p + fderiv ℝ F p q.2) ∧
      HasStrictFDerivAt (fun q : ℝ × E => Real.exp q.1 • F q.2) (L : (ℝ × E) →L[ℝ] V n)
        ((0 : ℝ), p) := by
  have hFp : H (F p) = 1 := hFS.self_of_nhds
  have hd := hF.hasStrictFDerivAt (by norm_num)
  have hHd : HasFDerivAt H (fderiv ℝ H (F p)) (F p) :=
    ((hH.1.differentiable (by simp)) _).hasFDerivAt
  have h0 : ∀ v, fderiv ℝ H (F p) (fderiv ℝ F p v) = 0 := by
    have h1 : HasFDerivAt (H ∘ F) _ p := hHd.comp p hd.hasFDerivAt
    have h2 : HasFDerivAt (H ∘ F) (0 : E →L[ℝ] ℝ) p := by
      refine (hasFDerivAt_const (1 : ℝ) p).congr_of_eventuallyEq ?_
      filter_upwards [hFS] with q hq using hq
    intro v
    exact DFunLike.congr_fun (h1.unique h2) v
  refine ⟨h0, ?_⟩
  let Λ : (ℝ × E) →L[ℝ] V n :=
    (ContinuousLinearMap.fst ℝ ℝ E).smulRight (F p) +
      (fderiv ℝ F p).comp (ContinuousLinearMap.snd ℝ ℝ E)
  have hΛ : ∀ q, Λ q = q.1 • F p + fderiv ℝ F p q.2 := fun q => rfl
  have hker : Function.Injective Λ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨r, v⟩ h
    rw [hΛ] at h
    have h1 := congrArg (fderiv ℝ H (F p)) h
    simp only [map_add, map_smul, map_zero, h0, add_zero, smul_eq_mul] at h1
    have hr : r = 0 := (mul_eq_zero.1 h1).resolve_right (hH.2.2 _ hFp).ne'
    subst hr
    simp only [zero_smul, zero_add] at h
    rw [(map_eq_zero_iff _ hinj).1 h]
    rfl
  have hfr : Module.finrank ℝ (ℝ × E) = Module.finrank ℝ (V n) := by
    rw [Module.finrank_prod, hE, Module.finrank_self, Module.finrank_fin_fun]; ring
  let L : (ℝ × E) ≃L[ℝ] V n :=
    (LinearEquiv.ofInjectiveOfFinrankEq (Λ : (ℝ × E) →ₗ[ℝ] V n) hker hfr).toContinuousLinearEquiv
  have hL : (L : (ℝ × E) →L[ℝ] V n) = Λ := ContinuousLinearMap.ext fun q => rfl
  refine ⟨L, fun q => rfl, ?_⟩
  rw [hL]
  have h3 : HasStrictFDerivAt (fun q : ℝ × E => Real.exp q.1)
      (Real.exp 0 • ContinuousLinearMap.fst ℝ ℝ E) ((0 : ℝ), p) :=
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := E) (p := ((0 : ℝ), p))).exp
  have h4 : HasStrictFDerivAt (fun q : ℝ × E => F q.2)
      ((fderiv ℝ F p).comp (ContinuousLinearMap.snd ℝ ℝ E)) ((0 : ℝ), p) :=
    HasStrictFDerivAt.comp ((0 : ℝ), p) (g := F) hd hasStrictFDerivAt_snd
  refine (h3.smul h4).congr_fderiv ?_
  ext q <;> simp [Λ]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2 * n + 1) (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (F : E → V n) (p : E) (hF : ContDiffAt ℝ 1 F p)
    (hFS : ∀ᶠ q in 𝓝 p, F q ∈ energySurface H) (hinj : Function.Injective (fderiv ℝ F p)) :
    (∀ v, fderiv ℝ H (F p) (fderiv ℝ F p v) = 0) ∧
    ∃ L : (ℝ × E) ≃L[ℝ] V n, (∀ q, L q = q.1 • F p + fderiv ℝ F p q.2) ∧
      HasStrictFDerivAt (fun q : ℝ × E => Real.exp q.1 • F q.2) (L : (ℝ × E) →L[ℝ] V n)
        ((0 : ℝ), p) :=
  exists_equiv_hasStrictFDerivAt_exp_smul_of_injective_aux hE H hH F p hF hFS hinj
