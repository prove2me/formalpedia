-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_marginal_laplace_equal_forces_exact_drift_jump_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:13:36.723446+00:00
-- url     : https://prove2.me/submissions/6604fe43-3148-4cef-a192-bcc5d3bb5e17

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Equality of the two original marginal exponential moments identifies
the true BV source path with physical drift minus its actual negative jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    let J : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0
    (∀ n : ℕ, Integrable (fun ω =>
      Real.exp (X.X (n : ℝ≥0) ω - (n : ℝ) * X.drift)) P) →
    (∀ n : ℕ, Integrable (fun ω =>
      Real.exp (-(J (n : ℝ≥0) ω))) P) →
    (∀ n : ℕ,
      (∫ ω, Real.exp (X.X (n : ℝ≥0) ω - (n : ℝ) * X.drift) ∂P) =
      (∫ ω, Real.exp (-(J (n : ℝ≥0) ω)) ∂P)) →
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift - J t ω := by
  dsimp only
  intro hIntA hIntB hMoment
  let J : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0
  let R : ℝ≥0 → Ω → ℝ := fun t ω =>
    (t : ℝ) * X.drift - X.X t ω - J t ω
  have hRzero : ∀ ω : Ω, R 0 ω = 0 := by
    intro ω
    have hz : ∀ u : ℝ≥0, ¬(0 < u ∧ u ≤ (0 : ℝ≥0)) := by
      intro u ⟨hu, hle⟩
      exact (not_lt_of_ge hle) hu
    have hsum : J 0 ω = 0 := by
      have hterm :
          (fun u : ℝ≥0 => if 0 < u ∧ u ≤ (0 : ℝ≥0) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
            else 0) = (fun _ => (0 : ℝ)) := by
        funext u
        exact if_neg (hz u)
      dsimp only [J]
      rw [hterm]
      exact tsum_zero
    dsimp only [R]
    rw [hsum]
    simp [X.X_zero ω]
  have hRmono : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => R t ω) := by
    simpa only [R, J] using
      (avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV)
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, R (n : ℝ≥0) ω = 0 := by
    intro n
    have hncast : ((n : ℝ≥0) : ℝ) = (n : ℝ) := by norm_cast
    have hRpos : ∀ᵐ ω ∂P, 0 ≤ R (n : ℝ≥0) ω := by
      filter_upwards [hRmono] with ω hmonoω
      calc 0 = R 0 ω := (hRzero ω).symm
           _ ≤ R (n : ℝ≥0) ω :=
             hmonoω (show (0 : ℝ≥0) ≤ (n : ℝ≥0) from zero_le)
    have hExpLe : ∀ᵐ ω ∂P,
        Real.exp (X.X (n : ℝ≥0) ω - (n : ℝ) * X.drift) ≤
          Real.exp (-(J (n : ℝ≥0) ω)) := by
      filter_upwards [hRpos] with ω hr
      have hle : X.X (n : ℝ≥0) ω - (n : ℝ) * X.drift ≤
          -(J (n : ℝ≥0) ω) := by
        dsimp [R] at hr
        rw [hncast] at hr
        linarith only [hr]
      exact Real.exp_le_exp.mpr hle
    have hDiffNonneg : 0 ≤ᵐ[P] (fun ω =>
        Real.exp (-(J (n : ℝ≥0) ω)) -
          Real.exp (X.X (n : ℝ≥0) ω - (n : ℝ) * X.drift)) := by
      filter_upwards [hExpLe] with ω he
      exact sub_nonneg.mpr he
    have hDiffInt : Integrable (fun ω =>
        Real.exp (-(J (n : ℝ≥0) ω)) -
          Real.exp (X.X (n : ℝ≥0) ω - (n : ℝ) * X.drift)) P :=
      (hIntB n).sub (hIntA n)
    have hDiffMean : (∫ ω,
        Real.exp (-(J (n : ℝ≥0) ω)) -
          Real.exp (X.X (n : ℝ≥0) ω - (n : ℝ) * X.drift) ∂P) = 0 := by
      rw [integral_sub (hIntB n) (hIntA n)]
      linarith only [hMoment n]
    have hDiffZero :=
      (integral_eq_zero_iff_of_nonneg_ae hDiffNonneg hDiffInt).mp hDiffMean
    filter_upwards [hDiffZero] with ω hz
    have hexp : Real.exp (X.X (n : ℝ≥0) ω - (n : ℝ) * X.drift) =
        Real.exp (-(J (n : ℝ≥0) ω)) := by
      have h := hz
      dsimp at h
      linarith only [h]
    have heq := Real.exp_injective hexp
    dsimp only [R]
    rw [hncast]
    linarith only [heq]
  have hNat : ∀ᵐ ω ∂P, ∀ n : ℕ, R (n : ℝ≥0) ω = 0 :=
    ae_all_iff.mpr hn
  filter_upwards [hRmono, hNat] with ω hmonoω hω
  intro t
  obtain ⟨n, htn⟩ := exists_nat_ge (t : ℝ)
  have htn' : t ≤ (n : ℝ≥0) := by exact_mod_cast htn
  have hlow : 0 ≤ R t ω := by
    calc 0 = R 0 ω := (hRzero ω).symm
         _ ≤ R t ω := hmonoω (show (0 : ℝ≥0) ≤ t from zero_le)
  have hhigh : R t ω ≤ 0 := by
    calc R t ω ≤ R (n : ℝ≥0) ω := hmonoω htn'
         _ = 0 := hω n
  have hz : R t ω = 0 := le_antisymm hhigh hlow
  dsimp only [R] at hz
  linarith only [hz]
