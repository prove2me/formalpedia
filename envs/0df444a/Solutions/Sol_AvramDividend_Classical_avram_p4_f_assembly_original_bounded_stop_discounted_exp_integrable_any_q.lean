-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:35:26.064641+00:00
-- url     : https://prove2.me/submissions/0babb79d-140f-4059-89ce-302a956ca1b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original bounded-stop Esscher density controls all finite-horizon discounts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω => Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P := by
  have hmean :=
    avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
      X θ hθ τ hstop H hbound
  have hgi : Integrable
      (fun ω => Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) P :=
    integrable_of_integral_eq_one hmean
  let M : ℝ := Real.exp (|X.ψ θ - q| * (H : ℝ))
  have hfactor : Measurable
      (fun ω => Real.exp ((X.ψ θ - q) * (τ ω : ℝ))) :=
    Real.measurable_exp.comp (measurable_const.mul hτmeas)
  have hfun : (fun ω => Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) =
      (fun ω => Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) *
        Real.exp ((X.ψ θ - q) * (τ ω : ℝ))) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hfmeas : AEStronglyMeasurable
      (fun ω => Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P := by
    rw [hfun]
    exact hgi.aestronglyMeasurable.fun_mul hfactor.aestronglyMeasurable
  have hBound : ∀ ω, Real.exp ((X.ψ θ - q) * (τ ω : ℝ)) ≤ M := by
    intro ω
    apply Real.exp_le_exp.mpr
    have hτnonneg : (0 : ℝ) ≤ (τ ω : ℝ) := NNReal.coe_nonneg _
    have hτH : (τ ω : ℝ) ≤ (H : ℝ) := by exact_mod_cast hbound ω
    have hcoef : X.ψ θ - q ≤ |X.ψ θ - q| := le_abs_self _
    have ha : (X.ψ θ - q) * (τ ω : ℝ) ≤
        |X.ψ θ - q| * (τ ω : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef hτnonneg
    have hb : |X.ψ θ - q| * (τ ω : ℝ) ≤
        |X.ψ θ - q| * (H : ℝ) :=
      mul_le_mul_of_nonneg_left hτH (abs_nonneg _)
    exact ha.trans hb
  have hmajor : Integrable
      (fun ω => M * Real.exp
        (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) P :=
    hgi.const_mul M
  have hminorNonneg : ∀ᵐ ω ∂P, 0 ≤
      Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) :=
    Filter.Eventually.of_forall (fun ω => le_of_lt (Real.exp_pos _))
  have hminorLE : ∀ᵐ ω ∂P,
      Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ≤
      M * Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) := by
    filter_upwards [] with ω
    calc
      Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) =
          Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) *
            Real.exp ((X.ψ θ - q) * (τ ω : ℝ)) :=
        congrFun hfun ω
      _ ≤ Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) * M :=
        mul_le_mul_of_nonneg_left (hBound ω) (le_of_lt (Real.exp_pos _))
      _ = M * Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) :=
        mul_comm _ _
  exact hmajor.mono_nonneg hfmeas hminorNonneg hminorLE