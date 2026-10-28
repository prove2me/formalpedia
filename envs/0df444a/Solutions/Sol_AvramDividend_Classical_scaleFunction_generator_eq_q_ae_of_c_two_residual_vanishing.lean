-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_c_two_residual_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:34:08.641349+00:00
-- url     : https://prove2.me/submissions/454fbb44-cbbb-465d-b536-f8e756d819f8

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
import Theorems.Thm_AvramDividend_Classical_ae_eq_Ioi_of_exponential_withDensity_eq
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_avram_laplace_ae_eq_of_nonnegative_20261026
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology
open AvramDividend.Classical

/-- The signed generator residual is uniquely determined almost everywhere
by its complete family of absolutely integrable Laplace transforms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioo 0 a))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by
  let R : ℝ → ℝ := fun x => X.generator W x - q * W x
  let f : ℝ → ℝ := fun x => R x + |R x|
  let g : ℝ → ℝ := fun x => |R x|
  let μ0 : Measure ℝ := volume.restrict (Ioi 0)
  obtain ⟨b, hb, hψ⟩ := psi_eventually_gt_of_standing X hX q hq
  have hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x := by
    intro x _
    dsimp [f]
    linarith [neg_le_abs (R x)]
  have hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x := by
    intro x _
    exact abs_nonneg _
  have hlap (θ : ℝ) (hθ : b < θ) :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * f x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * g x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * f x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * g x := by
    have hθ0 : 0 ≤ θ := le_trans hb (le_of_lt hθ)
    have hθψ : q < X.ψ θ := hψ θ (le_of_lt hθ)
    obtain ⟨hRi, hRzero⟩ := hweighted θ hθ0 hθψ
    have hRi' : Integrable (fun x : ℝ => Real.exp (-(θ * x)) * R x) μ0 := by
      simpa only [R, μ0] using hRi.integrable
    have hgi : Integrable (fun x : ℝ => Real.exp (-(θ * x)) * g x) μ0 := by
      simpa only [g, abs_mul, abs_of_pos (Real.exp_pos _)] using hRi'.abs
    have hfi : Integrable (fun x : ℝ => Real.exp (-(θ * x)) * f x) μ0 := by
      have hfadd :
          (fun x : ℝ => Real.exp (-(θ * x)) * f x) =
          (fun x : ℝ => Real.exp (-(θ * x)) * R x) +
          (fun x : ℝ => Real.exp (-(θ * x)) * g x) := by
        funext x
        simp [f, g, mul_add, Pi.add_apply]
      rw [hfadd]
      exact hRi'.add hgi
    refine ⟨hfi, hgi, ?_⟩
    have hsum :
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * f x) =
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * R x) +
          ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * g x := by
      simpa only [f, g, mul_add] using (integral_add hRi' hgi)
    rw [hsum]
    have hzero :
        (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * R x) = 0 := by
      simpa only [R] using hRzero
    rw [hzero, zero_add]
  have hae : f =ᵐ[μ0] g :=
    avram_laplace_ae_eq_of_nonnegative_20261026
      f g b hfnonneg hgnonneg hlap
  have hRzero : ∀ᵐ x ∂μ0, R x = 0 := by
    filter_upwards [hae] with x h
    dsimp [f, g] at h
    linarith
  have hlocal : ∀ᵐ x ∂(μ0.restrict (Ioo 0 a)), R x = 0 :=
    ae_restrict_of_ae hRzero
  have hset : Ioo (0 : ℝ) a ∩ Ioi 0 = Ioo 0 a :=
    Set.inter_eq_left.mpr (fun x hx => hx.1)
  have hmeasure : μ0.restrict (Ioo 0 a) = volume.restrict (Ioo 0 a) := by
    change (volume.restrict (Ioi (0 : ℝ))).restrict (Ioo 0 a) =
      volume.restrict (Ioo 0 a)
    rw [Measure.restrict_restrict isOpen_Ioo.measurableSet, hset]
  rw [hmeasure] at hlocal
  simpa only [R] using hlocal
