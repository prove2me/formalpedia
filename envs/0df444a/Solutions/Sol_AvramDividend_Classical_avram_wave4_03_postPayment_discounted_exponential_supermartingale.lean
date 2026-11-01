-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_postPayment_discounted_exponential_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:15:45.559502+00:00
-- url     : https://prove2.me/submissions/cb14a665-ba49-4a26-b2e4-dc0d18e93061

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_martingale_bounded_adapted_antitone_weight_supermartingale

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q) :
    Supermartingale (fun t ω =>
      Real.exp (θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q))
      𝓕.rightCont P := by
  obtain ⟨Y, hYX, hc, hσ, hν⟩ := levy_rightCont_process X
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)
  let a : ℝ≥0 → ℝ := fun t =>
    Real.exp ((t : ℝ) * (X.ψ θ - q))
  let b : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(θ * rightLimit D t ω))
  let v : ℝ≥0 → Ω → ℝ := fun t ω => a t * b t ω
  have hZ : Martingale Z 𝓕.rightCont P := by
    have hY := levy_compensated_exponential_martingale Y θ hθ
    simpa [Z, SpectrallyNegativeLevy.ψ, hYX, hc, hσ, hν] using hY
  have hZpos : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ Z t ω := by
    intro t
    filter_upwards [] with ω
    exact (Real.exp_pos _).le
  have hBadapt : Adapted 𝓕.rightCont b := by
    intro t
    exact ((measurable_const.mul
      (dividendStrategy_rightLimit_adapted_rightCont D hD t)).neg).exp
  have hBanti : ∀ ω, Antitone (fun t => b t ω) := by
    intro ω s t hst
    apply Real.exp_le_exp.mpr
    have hm := avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω hst
    have hmul := mul_le_mul_of_nonneg_left hm hθ
    linarith
  have hBbound : ∀ t ω, 0 < b t ω ∧ b t ω ≤ 1 := by
    intro t ω
    constructor
    · exact Real.exp_pos _
    · have hDnonneg : 0 ≤ D t ω := by
        have hm := (hD.2.1 ω) (zero_le : (0 : ℝ≥0) ≤ t)
        change D 0 ω ≤ D t ω at hm
        rw [hD.1 ω] at hm
        exact hm
      have hright : 0 ≤ rightLimit D t ω :=
        le_trans hDnonneg (dividendStrategy_le_rightLimit D hD ω t)
      have hle : -(θ * rightLimit D t ω) ≤ 0 :=
        neg_nonpos.mpr (mul_nonneg hθ hright)
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
  have haPos (t : ℝ≥0) : 0 ≤ a t := (Real.exp_pos _).le
  have haOne (t : ℝ≥0) : a t ≤ 1 := by
    dsimp [a]
    have hgap : X.ψ θ - q ≤ 0 := sub_nonpos.mpr hψ
    have ht : (0 : ℝ) ≤ (t : ℝ) := NNReal.coe_nonneg t
    have hle : (t : ℝ) * (X.ψ θ - q) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht hgap
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
  have haAnti : Antitone a := by
    intro s t hst
    dsimp [a]
    apply Real.exp_le_exp.mpr
    have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    exact mul_le_mul_of_nonpos_right hst' (sub_nonpos.mpr hψ)
  have hvAdapt : Adapted 𝓕.rightCont v := by
    intro t
    exact measurable_const.mul (hBadapt t)
  have hvBound : ∀ t ω, 0 ≤ v t ω ∧ v t ω ≤ 1 := by
    intro t ω
    constructor
    · exact mul_nonneg (haPos t) (hBbound t ω).1.le
    · calc
        a t * b t ω ≤ 1 * b t ω :=
          mul_le_mul_of_nonneg_right (haOne t) (hBbound t ω).1.le
        _ ≤ 1 := by simpa only [one_mul] using (hBbound t ω).2
  have hvAnti : ∀ ω, Antitone (fun t => v t ω) := by
    intro ω s t hst
    exact mul_le_mul (haAnti hst) (hBanti ω hst)
      (hBbound t ω).1.le (haPos s)
  have hS :=
    martingale_bounded_adapted_antitone_weight_supermartingale
      Z hZ hZpos v hvAdapt hvBound hvAnti
  have heq :
      (fun t ω => v t ω * Z t ω) =
      (fun t ω => Real.exp (θ * (X.X t ω - rightLimit D t ω) -
        (t : ℝ) * q)) := by
    funext t ω
    dsimp [v, a, b, Z]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hS
  have hScaled := hS.smul_nonneg (Real.exp_pos (θ * x)).le
  have heq' :
      (Real.exp (θ * x)) •
        (fun t ω => Real.exp
          (θ * (X.X t ω - rightLimit D t ω) - (t : ℝ) * q)) =
      (fun t ω => Real.exp
        (θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q)) := by
    funext t ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq'] at hScaled
  exact hScaled
