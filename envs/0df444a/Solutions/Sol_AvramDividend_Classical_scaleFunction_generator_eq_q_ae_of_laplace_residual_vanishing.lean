-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T14:43:22.166447+00:00
-- url     : https://prove2.me/submissions/c4c4e2cc-ef83-4324-95f5-51586ff36c9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing_parts

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (b : ℝ)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by
  let R : ℝ → ℝ := fun x => X.generator W x - q * W x
  have hRcont : ContinuousOn R (Ioi 0) := by
    simpa [R] using hcont
  have hRpcont : ContinuousOn (fun x => max (R x) 0) (Ioi 0) := by
    refine (hRcont.sup continuousOn_const).mono ?_
    intro x hx
    exact hx
  have hRmcont : ContinuousOn (fun x => max (-(R x)) 0) (Ioi 0) := by
    refine (hRcont.neg.sup continuousOn_const).mono ?_
    intro x hx
    exact hx
  have hdomplus : ∀ x : ℝ, max (X.generator W x - q * W x) 0 ≤
      |X.generator W x - q * W x| := by
    intro x
    calc max (X.generator W x - q * W x) 0 ≤
        max |X.generator W x - q * W x| |X.generator W x - q * W x| :=
          max_le_max (le_abs_self _) (abs_nonneg _)
      _ = |X.generator W x - q * W x| := max_self _
  have hdomminus : ∀ x : ℝ, max (-(X.generator W x - q * W x)) 0 ≤
      |X.generator W x - q * W x| := by
    intro x
    exact max_le (neg_le_abs _) (abs_nonneg _)
  -- Each discounted part is dominated by the discounted residual, so the
  -- integrability of the residual gives the integrability of both parts.
  have hint : ∀ (p : ℝ → ℝ), (∀ x : ℝ, 0 ≤ p x) →
      (∀ x : ℝ, p x ≤ |X.generator W x - q * W x|) →
      ∀ θ : ℝ, b < θ → ContinuousOn p (Ioi 0) →
        IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * p x) (Ioi (0 : ℝ)) := by
    intro p hp hdom θ hθ hpcont
    have hinter := (hlap θ hθ).1
    rw [IntegrableOn] at hinter
    have hle : ∀ᵐ x ∂(Measure.restrict (MeasureTheory.MeasureSpace.volume) (Ioi (0 : ℝ))),
        ‖Real.exp (-(θ * x)) * p x‖ ≤
          ‖Real.exp (-(θ * x)) * (X.generator W x - q * W x)‖ := by
      have hmem : ∀ᵐ x ∂(Measure.restrict (MeasureTheory.MeasureSpace.volume) (Ioi (0 : ℝ))),
          x ∈ Ioi (0 : ℝ) := ae_restrict_mem measurableSet_Ioi
      filter_upwards [hmem] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
        abs_of_nonneg (hp x), Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hdom x) (Real.exp_nonneg _)
    have hsm : AEStronglyMeasurable (fun x : ℝ => Real.exp (-(θ * x)) * p x)
        (Measure.restrict (MeasureTheory.MeasureSpace.volume) (Ioi (0 : ℝ))) := by
      have hc : Continuous (fun x : ℝ => Real.exp (-(θ * x))) := by fun_prop
      exact ContinuousOn.aestronglyMeasurable (hc.continuousOn.mul hpcont) measurableSet_Ioi
    exact Integrable.mono hinter hsm hle
  have hintp (θ : ℝ) (hθ : b < θ) :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        max (X.generator W x - q * W x) 0) (Ioi (0 : ℝ)) :=
    hint (fun x => max (X.generator W x - q * W x) 0)
      (fun x => le_max_right (X.generator W x - q * W x) 0) hdomplus θ hθ
      (by simpa [R] using hRpcont)
  have hintm (θ : ℝ) (hθ : b < θ) :
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        max (-(X.generator W x - q * W x)) 0) (Ioi (0 : ℝ)) :=
    hint (fun x => max (-(X.generator W x - q * W x)) 0)
      (fun x => le_max_right (-(X.generator W x - q * W x)) 0) hdomminus θ hθ
      (by simpa [R] using hRmcont)
  -- The residual splits into its two parts, so the vanishing of the transform
  -- of the residual is the agreement of the transforms of the two parts.
  have hlapeq (θ : ℝ) (hθ : b < θ) :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        max (X.generator W x - q * W x) 0) =
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        max (-(X.generator W x - q * W x)) 0) := by
    -- The pointwise split of the residual into its two parts.  The two
    -- reductions are stated at the top level, where the `max` of the goal
    -- occurs, because a rewrite cannot abstract a pattern under a binder.
    have hsplit (x : ℝ) :
        Real.exp (-(θ * x)) * max (X.generator W x - q * W x) 0 =
        Real.exp (-(θ * x)) * (X.generator W x - q * W x) +
          Real.exp (-(θ * x)) * max (-(X.generator W x - q * W x)) 0 := by
      rcases le_total (X.generator W x - q * W x) 0 with h | h
      · have hzero1 : max (X.generator W x - q * W x) 0 = 0 := max_eq_right h
        have hzero2 : max (-(X.generator W x - q * W x)) 0 =
            -(X.generator W x - q * W x) := max_eq_left (neg_nonneg.mpr h)
        rw [hzero1, hzero2]
        ring
      · have hzero1 : max (X.generator W x - q * W x) 0 =
            X.generator W x - q * W x := max_eq_left h
        have hzero2 : max (-(X.generator W x - q * W x)) 0 = 0 :=
          max_eq_right (neg_nonpos.mpr h)
        rw [hzero1, hzero2]
        ring
    have hadd : (fun x : ℝ => Real.exp (-(θ * x)) *
          max (X.generator W x - q * W x) 0) =
        (fun x : ℝ => Real.exp (-(θ * x)) * (X.generator W x - q * W x)) +
          (fun x : ℝ => Real.exp (-(θ * x)) *
            max (-(X.generator W x - q * W x)) 0) := by
      funext x
      exact hsplit x
    have hconv : (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
          max (X.generator W x - q * W x) 0) =
        (∫ x in Ioi (0 : ℝ), (Real.exp (-(θ * x)) *
          (X.generator W x - q * W x) +
          Real.exp (-(θ * x)) * max (-(X.generator W x - q * W x)) 0)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => congrFun hadd x))
    have hres : Integrable (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x))
        (Measure.restrict (MeasureTheory.MeasureSpace.volume) (Ioi (0 : ℝ))) := by
      have h := (hlap θ hθ).1
      rw [IntegrableOn] at h
      exact h
    have hneg : Integrable (fun x : ℝ => Real.exp (-(θ * x)) *
        max (-(X.generator W x - q * W x)) 0)
        (Measure.restrict (MeasureTheory.MeasureSpace.volume) (Ioi (0 : ℝ))) := by
      have h := hintm θ hθ
      rw [IntegrableOn] at h
      exact h
    rw [hconv, integral_add hres hneg, (hlap θ hθ).2]
    ring
  exact scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing_parts
    X q W hW a ha b hcont
    (fun θ hθ => ⟨hintp θ hθ, hintm θ hθ, hlapeq θ hθ⟩)
