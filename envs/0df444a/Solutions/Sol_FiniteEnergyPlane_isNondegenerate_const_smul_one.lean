-- Prove2me | solution 1 for FiniteEnergyPlane.isNondegenerate_const_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T22:33:55.858567+00:00
-- url     : https://prove2.me/submissions/955eed24-a5f8-4982-8220-4d3d41fbcc05

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique



/-!
# Constant loops `c • 1`, `c ∈ (0, 2π)` (source of the published
`FiniteEnergyPlane.isNondegenerate_const_smul_one`)
-/

namespace FiniteEnergyPlane.QTgND

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Tg-ND: constant loops `c • 1` -/

lemma tg_hasDerivAt_mat_iff {m : ℕ} {f : ℝ → Mat m} {f' : Mat m} {t : ℝ} :
    HasDerivAt f f' t ↔ ∀ i j, HasDerivAt (fun s => f s i j) (f' i j) t := by
  constructor
  · intro h i j
    exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j
  · intro h
    exact hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => h i j

lemma tg_fund_const (m : ℕ) (c : ℝ) :
    IsFundamentalSolution (fun _ : ℝ => c • (1 : Mat m))
      (fun t => Real.cos (c * t) • (1 : Mat m) + Real.sin (c * t) • J₀ m) := by
  refine ⟨by simp, fun t => ?_⟩
  have hl : HasDerivAt (fun y : ℝ => c * y) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have hJ : J₀ m * J₀ m = -1 := Matrix.J_squared (Fin m) ℝ
  have key : J₀ m * (c • (1 : Mat m)) *
      (Real.cos (c * t) • (1 : Mat m) + Real.sin (c * t) • J₀ m) =
      (-Real.sin (c * t) * c) • (1 : Mat m) + (Real.cos (c * t) * c) • J₀ m := by
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hJ]
    module
  rw [key, tg_hasDerivAt_mat_iff]
  intro i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact ((hl.cos).mul_const _).add ((hl.sin).mul_const _)

lemma det_add_smul_J_ne_zero (m : ℕ) (α β : ℝ) (h : α ^ 2 + β ^ 2 ≠ 0) :
    (α • (1 : Mat m) + β • J₀ m).det ≠ 0 := by
  have hJ : J₀ m * J₀ m = -1 := Matrix.J_squared (Fin m) ℝ
  have hprod : (α • (1 : Mat m) + β • J₀ m) * (α • (1 : Mat m) - β • J₀ m) =
      (α ^ 2 + β ^ 2) • (1 : Mat m) := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hJ]
    module
  intro h0
  have := congrArg Matrix.det hprod
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ h this.symm

lemma cos_ne_one_of_mem {c : ℝ} (hc : c ∈ Ioo 0 (2 * π)) : Real.cos c ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff c).1 h
  have h1 : (0 : ℝ) < k * (2 * π) := hk ▸ hc.1
  have h2 : k * (2 * π) < 1 * (2 * π) := by rw [hk, one_mul]; exact hc.2
  have hk0 : (0 : ℝ) < k := pos_of_mul_pos_left h1 (by positivity)
  have hk1 : (k : ℝ) < 1 := lt_of_mul_lt_mul_right h2 (by positivity)
  have : (0 : ℤ) < k := by exact_mod_cast hk0
  have : k < (1 : ℤ) := by exact_mod_cast hk1
  omega

/-- Tg-ND. -/
theorem isNondegenerate_const_smul_one (m : ℕ) (c : ℝ) (hc : c ∈ Ioo 0 (2 * π)) :
    IsSymLoop (fun _ : ℝ => c • (1 : Mat m)) ∧ IsNondegenerate (fun _ : ℝ => c • (1 : Mat m)) := by
  refine ⟨⟨continuous_const, fun _ => rfl, fun _ => (Matrix.isSymm_one).smul c⟩, ?_⟩
  intro Ψ hΨ
  obtain ⟨Φ, _, huniq⟩ := fundamentalSolution_existsUnique m (fun _ : ℝ => c • (1 : Mat m))
    continuous_const
  have hE : Ψ = fun t => Real.cos (c * t) • (1 : Mat m) + Real.sin (c * t) • J₀ m :=
    (huniq Ψ hΨ).trans (huniq _ (tg_fund_const m c)).symm
  rw [hE]
  have h1 : (1 : Mat m) - (Real.cos (c * 1) • (1 : Mat m) + Real.sin (c * 1) • J₀ m) =
      (1 - Real.cos c) • (1 : Mat m) + (-Real.sin c) • J₀ m := by
    simp only [mul_one]; module
  rw [h1]
  refine det_add_smul_J_ne_zero m _ _ fun h0 => cos_ne_one_of_mem hc ?_
  nlinarith [sq_nonneg (1 - Real.cos c), sq_nonneg (Real.sin c)]

end

end FiniteEnergyPlane.QTgND

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (m : ℕ) (c : ℝ) (hc : c ∈ Ioo 0 (2 * π)) :
    IsSymLoop (fun _ : ℝ => c • (1 : Mat m)) ∧ IsNondegenerate (fun _ : ℝ => c • (1 : Mat m)) :=
  FiniteEnergyPlane.QTgND.isNondegenerate_const_smul_one m c hc
