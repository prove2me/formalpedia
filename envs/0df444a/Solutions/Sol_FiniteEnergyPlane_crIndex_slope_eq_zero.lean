-- Prove2me | solution 1 for FiniteEnergyPlane.crIndex_slope_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T22:38:36.500199+00:00
-- url     : https://prove2.me/submissions/d35bbc4c-e69f-466f-9ad5-57495ae1b855

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_isNondegenerate_const_smul_one
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_bijective
import Theorems.Thm_CauchyRiemannIndex_crIndex_eq_of_homotopy
import Theorems.Thm_CauchyRiemannIndex_index_formula
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique



/-!
# Slope weights (local helper definition, not published as a definition)

`IsSlopeWeight χ a b`: `χ` is smooth, with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`.
-/

namespace FiniteEnergyPlane

open scoped ContDiff

/-- `χ` is smooth with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`. -/
def IsSlopeWeight (χ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ (∀ s ≤ -1, deriv χ s = a) ∧ ∀ s ≥ 1, deriv χ s = b

/-! ### Slope weights are affine near the ends -/

theorem IsSlopeWeight.eq_right {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : 1 ≤ s) : χ s = χ 1 + b * (s - 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have hb : deriv χ c = b := h.2.2 c hc.1.le
  rw [hb, eq_div_iff (by linarith)] at hc'
  linarith

theorem IsSlopeWeight.eq_left {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : s ≤ -1) : χ s = χ (-1) + a * (s + 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have ha : deriv χ c = a := h.2.1 c hc.2.le
  rw [ha, eq_div_iff (by linarith)] at hc'
  linarith


end FiniteEnergyPlane

/-!
# The slope coefficient `χ'(s) • 1` is asymptotic to constant loops (local helper)
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Tg-As: the slope coefficient is asymptotic to constant loops -/

lemma deriv_slope_bdd {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) :
    ∃ K, ∀ s, |deriv χ s| ≤ K := by
  have hc : Continuous (deriv χ) := hχ.1.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B (max |a| |b|), fun s => ?_⟩
  rcases le_or_gt s (-1) with h | h
  · rw [hχ.2.1 s h]; exact (le_max_left _ _).trans (le_max_right _ _)
  rcases le_or_gt 1 s with h' | h'
  · rw [hχ.2.2 s h']; exact (le_max_right _ _).trans (le_max_right _ _)
  · have := hB s ⟨h.le, h'.le⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- The homotopy `(1 - τ) χ'(s) + τ c`. -/
def slopeHom (χ : ℝ → ℝ) (c : ℝ) (τ : unitInterval) (x : ℝ × ℝ) : Mat 1 :=
  ((1 - (τ : ℝ)) * deriv χ x.1 + (τ : ℝ) * c) • (1 : Mat 1)

lemma slopeHom_isAsymptoticTo {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) (c : ℝ)
    (τ : unitInterval) :
    IsAsymptoticTo (slopeHom χ c τ) (fun _ => ((1 - (τ : ℝ)) * b + (τ : ℝ) * c) • (1 : Mat 1))
      (fun _ => ((1 - (τ : ℝ)) * a + (τ : ℝ) * c) • (1 : Mat 1)) := by
  have hc : Continuous (deriv χ) := hχ.1.continuous_deriv (by simp)
  refine ⟨?_, fun s t => rfl, fun ε hε => ⟨1, fun s t i j => ⟨fun hs => ?_, fun hs => ?_⟩⟩⟩
  · unfold slopeHom
    exact ((continuous_const.mul (hc.comp continuous_fst)).add continuous_const).smul
      continuous_const
  · simp only [slopeHom, hχ.2.2 s hs, sub_self, abs_zero]; exact hε.le
  · simp only [slopeHom, hχ.2.1 s hs, sub_self, abs_zero]; exact hε.le

lemma convex_mem {a c : ℝ} (ha : a ∈ Ioo 0 (2 * π)) (hc : c ∈ Ioo 0 (2 * π))
    (τ : unitInterval) : (1 - (τ : ℝ)) * a + (τ : ℝ) * c ∈ Ioo 0 (2 * π) := by
  have h0 : 0 ≤ (τ : ℝ) := τ.2.1
  have h1 : (τ : ℝ) ≤ 1 := τ.2.2
  have hm : 0 < min a c := lt_min ha.1 hc.1
  have hM : max a c < 2 * π := max_lt ha.2 hc.2
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (min_le_left a c)),
      mul_nonneg h0 (sub_nonneg.2 (min_le_right a c))]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (le_max_left a c)),
      mul_nonneg h0 (sub_nonneg.2 (le_max_right a c))]

end

end FiniteEnergyPlane

/-!
# Q-Tg `crApply_slope_bijective` (local, NOT published)

* Tg-ND `isNondegenerate_const_smul_one`: `c • 1` is a nondegenerate symmetric loop, `c ∈ (0, 2π)`.
* Tg-As: `χ'(s) • 1` is asymptotic to `b • 1` / `a • 1`.
* Tg-Ix `crIndex_slope_eq_zero`: index `0`, through the homotopy `(1-τ) χ' + τ a` to a
  translation-invariant operator (bijective by 4.11).
* Tg-Inj and the glue (Fredholm + index `0` + injective ⇒ onto) are in `Scratch/JWQ_TgGlue.lean`,
  above the Tg-Inj layers `Scratch/JWQ_TgInj1`-`5`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Tg-Ix: index zero -/

lemma crIndex_eq_zero_of_bijective (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : ℝ × ℝ → Mat 1)
    (hk : crKernel p S = ⊥) (hr : crRange p S = ⊤) : crIndex p S = 0 := by
  unfold crIndex
  rw [hk, hr, finrank_bot]
  have : Subsingleton (LpCyl 1 p ⧸ (⊤ : Submodule ℝ (LpCyl 1 p))) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  rw [Module.finrank_zero_of_subsingleton]
  simp

/-- Tg-Ix. -/
theorem crIndex_slope_eq_zero_aux (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (a b : ℝ) (ha : a ∈ Ioo 0 (2 * π)) (hb : b ∈ Ioo 0 (2 * π))
    (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ a b) :
    crIndex p (fun x => deriv χ x.1 • (1 : Mat 1)) = 0 := by
  obtain ⟨K, hK⟩ := deriv_slope_bdd hχ
  have hP := fun τ => isNondegenerate_const_smul_one 1 _ (convex_mem hb ha τ)
  have hM := fun τ => isNondegenerate_const_smul_one 1 _ (convex_mem ha ha τ)
  have hhom := crIndex_eq_of_homotopy 1 p hp hp' (slopeHom χ a)
    (fun τ _ => ((1 - (τ : ℝ)) * b + (τ : ℝ) * a) • (1 : Mat 1))
    (fun τ _ => ((1 - (τ : ℝ)) * a + (τ : ℝ) * a) • (1 : Mat 1))
    (fun τ => (hP τ).1) (fun τ => (hM τ).1) (fun τ => (hP τ).2) (fun τ => (hM τ).2)
    (fun τ => slopeHom_isAsymptoticTo hχ a τ) (fun τ ε hε => ?_)
  · have h0 : slopeHom χ a 0 = fun x => deriv χ x.1 • (1 : Mat 1) := by
      funext x; simp [slopeHom]
    have h1 : slopeHom χ a 1 = fun x : ℝ × ℝ => (fun _ : ℝ => a • (1 : Mat 1)) x.2 := by
      funext x; simp [slopeHom]
    rw [← h0, hhom, h1]
    obtain ⟨hk, hr⟩ := translationInvariant_bijective 1 p hp hp' (fun _ : ℝ => a • (1 : Mat 1))
      (isNondegenerate_const_smul_one 1 a ha).1 (isNondegenerate_const_smul_one 1 a ha).2
    exact crIndex_eq_zero_of_bijective p _ hk hr
  · -- uniform continuity of the homotopy in `τ`
    have hL : 0 ≤ K + |a| := add_nonneg ((abs_nonneg _).trans (hK 0)) (abs_nonneg _)
    refine ⟨ε / (K + |a| + 1), by positivity, fun σ hσ x i j => ?_⟩
    have hd : slopeHom χ a σ x i j - slopeHom χ a τ x i j =
        ((σ : ℝ) - τ) * (a - deriv χ x.1) * (1 : Mat 1) i j := by
      simp only [slopeHom, Matrix.smul_apply, smul_eq_mul]; ring
    rw [hd, abs_mul, abs_mul]
    have h1 : |(1 : Mat 1) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    have h2 : |a - deriv χ x.1| ≤ K + |a| := by
      have := abs_sub (a) (deriv χ x.1); have := hK x.1; linarith
    have h3 : |(σ : ℝ) - τ| ≤ ε / (K + |a| + 1) := by
      have : dist σ τ = |(σ : ℝ) - τ| := Subtype.dist_eq σ τ ▸ Real.dist_eq _ _
      linarith
    calc |(σ : ℝ) - τ| * |a - deriv χ x.1| * |(1 : Mat 1) i j|
        ≤ ε / (K + |a| + 1) * (K + |a| + 1) * 1 := by
          gcongr
          linarith
      _ = ε := by field_simp


end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (a b : ℝ) (ha : a ∈ Ioo 0 (2 * π)) (hb : b ∈ Ioo 0 (2 * π))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχa : ∀ s ≤ -1, deriv χ s = a)
    (hχb : ∀ s ≥ 1, deriv χ s = b) :
    crIndex p (fun x => deriv χ x.1 • (1 : Mat 1)) = 0 :=
  FiniteEnergyPlane.crIndex_slope_eq_zero_aux p hp hp' a b ha hb χ ⟨hχ, hχa, hχb⟩
