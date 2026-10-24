-- Prove2me | solution 1 for FiniteEnergyPlane.exists_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-23T16:07:30.732159+00:00
-- url     : https://prove2.me/submissions/400be056-f26a-4703-85ca-6c8ae4e82972

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Support



namespace FiniteEnergyPlane

open Set Filter Topology

/-- There is a `C¹` function `φ : ℝ → ℝ` with values in `[0, 1]`, equal to `1` on `(-∞, 1/4]`
and to `0` on `[3/4, ∞)`, with `φ' ≤ 0` everywhere, `φ' = 0` on `(3/4, ∞)`, and `φ'` bounded. -/
theorem exists_cutoff_aux : ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ (∀ t, t ≤ 1 / 4 → φ t = 1) ∧
    (∀ t, 3 / 4 ≤ t → φ t = 0) ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, deriv φ t ≤ 0) ∧
    (∀ t, 3 / 4 < t → deriv φ t = 0) ∧ ∃ M, ∀ t, |deriv φ t| ≤ M := by
  set φ : ℝ → ℝ := fun t => Real.smoothTransition (3 / 2 - 2 * t) with hφ
  have hc : ContDiff ℝ 1 φ :=
    (Real.smoothTransition.contDiff (n := 1)).comp
      (contDiff_const.sub (contDiff_const.mul contDiff_id))
  have h1 : ∀ t, t ≤ 1 / 4 → φ t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le (by linarith)
  have h0 : ∀ t, 3 / 4 ≤ t → φ t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hanti : Antitone φ := fun a b hab =>
    Real.smoothTransition.monotone (by linarith)
  have hd0 : ∀ t, 3 / 4 < t → deriv φ t = 0 := by
    intro t ht
    have : φ =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds ht] with y hy using h0 y (le_of_lt hy)
    rw [this.deriv_eq]; simp
  have hd1 : ∀ t, t < 1 / 4 → deriv φ t = 0 := by
    intro t ht
    have : φ =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds ht] with y hy using h1 y (le_of_lt hy)
    rw [this.deriv_eq]; simp
  have hcs : HasCompactSupport (deriv φ) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 / 4 : ℝ)) (b := 3 / 4)) ?_
    intro t ht
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact hd1 t ht
    · exact hd0 t ht
  have hdc : Continuous (deriv φ) := hc.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support hcs
  exact ⟨φ, hc, h1, h0, fun t => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun t => hanti.deriv_nonpos, hd0, M, fun t => by simpa [Real.norm_eq_abs] using hM t⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open Set Filter Topology

theorem solution : ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ (∀ t, t ≤ 1 / 4 → φ t = 1) ∧
    (∀ t, 3 / 4 ≤ t → φ t = 0) ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, deriv φ t ≤ 0) ∧
    (∀ t, 3 / 4 < t → deriv φ t = 0) ∧ ∃ M, ∀ t, |deriv φ t| ≤ M :=
  exists_cutoff_aux
