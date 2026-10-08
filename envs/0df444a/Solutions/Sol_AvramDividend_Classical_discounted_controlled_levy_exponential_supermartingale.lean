-- Prove2me | solution 1 for AvramDividend.Classical.discounted_controlled_levy_exponential_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:26:43.627539+00:00
-- url     : https://prove2.me/submissions/f1da38f1-a81e-465f-bc87-4e25a550df4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_dividend_exponential_factor_package
import Theorems.Thm_AvramDividend_Classical_martingale_bounded_adapted_antitone_weight_supermartingale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q) :
    Supermartingale (fun t ω =>
      Real.exp (θ * (X.X t ω - D t ω) - (t : ℝ) * q)) 𝓕 P := by
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)
  let a : ℝ≥0 → ℝ := fun t =>
    Real.exp ((t : ℝ) * (X.ψ θ - q))
  let b : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(θ * D t ω))
  let w : ℝ≥0 → Ω → ℝ := fun t ω => a t * b t ω
  have hZ : Martingale Z 𝓕 P :=
    levy_compensated_exponential_martingale X θ hθ
  have hZpos : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ Z t ω := by
    intro t
    filter_upwards [] with ω
    exact (Real.exp_pos _).le
  obtain ⟨hBadapt, hBanti, hBbounded⟩ :=
    dividend_exponential_factor_package (P := P) D hD θ hθ
  have hApos (t : ℝ≥0) : 0 ≤ a t := (Real.exp_pos _).le
  have hAone (t : ℝ≥0) : a t ≤ 1 := by
    dsimp [a]
    have hgap : X.ψ θ - q ≤ 0 := sub_nonpos.mpr hψ
    have htnonneg : (0 : ℝ) ≤ (t : ℝ) := NNReal.coe_nonneg t
    have hle : (t : ℝ) * (X.ψ θ - q) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos htnonneg hgap
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
  have hAanti : Antitone a := by
    intro s t hst
    dsimp [a]
    apply Real.exp_le_exp.mpr
    have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    exact mul_le_mul_of_nonpos_right hst' (sub_nonpos.mpr hψ)
  have hwAdapt : Adapted 𝓕 w := by
    intro t
    exact measurable_const.mul (hBadapt t)
  have hwBounded : ∀ t ω, 0 ≤ w t ω ∧ w t ω ≤ 1 := by
    intro t ω
    dsimp [w]
    constructor
    · exact mul_nonneg (hApos t) (hBbounded t ω).1.le
    · calc
        a t * b t ω ≤ 1 * b t ω :=
          mul_le_mul_of_nonneg_right (hAone t) (hBbounded t ω).1.le
        _ ≤ 1 := by simpa only [one_mul] using (hBbounded t ω).2
  have hwAnti : ∀ ω, Antitone (fun t => w t ω) := by
    intro ω s t hst
    dsimp [w]
    exact mul_le_mul (hAanti hst) (hBanti ω hst)
      (hBbounded t ω).1.le (hApos s)
  have hS :=
    martingale_bounded_adapted_antitone_weight_supermartingale
      Z hZ hZpos w hwAdapt hwBounded hwAnti
  have heq :
      (fun t ω => w t ω * Z t ω) =
      (fun t ω => Real.exp (θ * (X.X t ω - D t ω) - (t : ℝ) * q)) := by
    funext t ω
    dsimp [w, a, b, Z]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hS
  exact hS
