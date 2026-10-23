-- Prove2me | solution 1 for AvramDividend.Classical.positive_causal_laplace_local_le_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:13:28.0969+00:00
-- url     : https://prove2.me/submissions/ee36fe1a-e7a8-426f-92e3-f64b42113dc1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_real_laplace_causal_convolution
import Theorems.Thm_AvramDividend_Classical_positive_weighted_causal_convolution_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (f g : ℝ → ℝ) (θ R : ℝ) (hR : 0 ≤ R)
    (hf : IntegrableOn (fun t : ℝ => Real.exp (-θ * t) * f t)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => Real.exp (-θ * t) * g t)
      (Ioi (0 : ℝ)) volume)
    (hfn : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hgn : ∀ t : ℝ, 0 ≤ t → 0 ≤ g t) :
    (∫ x in Ioc (0 : ℝ) R, Real.exp (-θ * x) *
      (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) ∂volume) ≤
      (∫ s in Ioi (0 : ℝ), Real.exp (-θ * s) * f s ∂volume) *
      (∫ t in Ioi (0 : ℝ), Real.exp (-θ * t) * g t ∂volume) := by
  let H : ℝ → ℝ := fun x =>
    Real.exp (-θ * x) *
      (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume)
  have hHintegrable : IntegrableOn H (Ioi (0 : ℝ)) volume := by
    simpa only [H, neg_mul] using
      (positive_weighted_causal_convolution_integrable f g θ
        (by simpa only [neg_mul] using hf)
        (by simpa only [neg_mul] using hg))
  have hHnonneg : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ H x := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    have hinner : 0 ≤ (∫ s in Ioc (0 : ℝ) x,
        f s * g (x - s) ∂volume) := by
      apply setIntegral_nonneg measurableSet_Ioc
      intro s hs
      exact mul_nonneg (hfn s (le_of_lt hs.1))
        (hgn (x - s) (sub_nonneg.mpr hs.2))
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) hinner
  have hsubset : (Ioc (0 : ℝ) R) ≤ᵐ[volume] (Ioi (0 : ℝ)) :=
    Filter.Eventually.of_forall (by intro x hx; exact hx.1)
  have hle :
      (∫ x in Ioc (0 : ℝ) R, H x ∂volume) ≤
      (∫ x in Ioi (0 : ℝ), H x ∂volume) :=
    setIntegral_mono_set hHintegrable hHnonneg hsubset
  have hfactor :
      (∫ x in Ioi (0 : ℝ), H x ∂volume) =
      (∫ s in Ioi (0 : ℝ), Real.exp (-θ * s) * f s ∂volume) *
      (∫ t in Ioi (0 : ℝ), Real.exp (-θ * t) * g t ∂volume) := by
    have h := positive_real_laplace_causal_convolution f g θ hf hg
    calc
      (∫ x in Ioi (0 : ℝ), H x ∂volume) =
        ∫ x in Ioi (0 : ℝ), ∫ s in Ioc (0 : ℝ) x,
          Real.exp (-θ * x) * (f s * g (x - s)) ∂volume ∂volume := by
            simp only [H, integral_const_mul]
      _ = _ := h
  exact (show (∫ x in Ioc (0 : ℝ) R, H x ∂volume) ≤ _ from
    hle.trans_eq hfactor)
