-- Prove2me | solution 1 for AvramDividend.Classical.chat03_scale_laplace_pointwise_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:52:16.609992+00:00
-- url     : https://prove2.me/submissions/e0d2bb38-a222-4751-bfd6-c16d8576e4cd

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Chat 03. Derive a local exponential envelope from the canonical Laplace
transform of W. This is a nontrivial analytic input to fixed-horizon L² UI.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (hy : 0 ≤ y) :
    Real.exp (-(θ * (y + 1))) * W y ≤ (X.ψ θ - q)⁻¹ := by
  let f : ℝ → ℝ := fun z => Real.exp (-(θ * z)) * W z
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) :=
    (hW.2.2.2.2 θ hθ hψ).1
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact mul_nonneg (Real.exp_nonneg _) (hW.2.1 z hz.le)
  have hsubset : Ioc y (y + 1) ⊆ Ioi (0 : ℝ) := by
    intro z hz
    exact lt_of_le_of_lt hy hz.1
  have hfi_small : IntegrableOn f (Ioc y (y + 1)) :=
    hfi.mono_set hsubset
  have hconstant : IntegrableOn
      (fun _ : ℝ => Real.exp (-(θ * (y + 1))) * W y)
      (Ioc y (y + 1)) := by
    exact integrableOn_const measure_Ioc_lt_top.ne
  have hpoint : ∀ z ∈ Ioc y (y + 1),
      Real.exp (-(θ * (y + 1))) * W y ≤ f z := by
    intro z hz
    have hmono : W y ≤ W z :=
      hW.2.2.2.1 (Set.mem_Ici.mpr hy)
        (Set.mem_Ici.mpr (le_trans hy hz.1.le)) hz.1.le
    have he : Real.exp (-(θ * (y + 1))) ≤
        Real.exp (-(θ * z)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left hz.2 hθ)
    calc
      Real.exp (-(θ * (y + 1))) * W y ≤
          Real.exp (-(θ * z)) * W y :=
        mul_le_mul_of_nonneg_right he (hW.2.1 y hy)
      _ ≤ Real.exp (-(θ * z)) * W z :=
        mul_le_mul_of_nonneg_left hmono (Real.exp_nonneg _)
  have hlow := setIntegral_ge_of_const_le_real
    (s := Ioc y (y + 1)) measurableSet_Ioc
    (by simp) hpoint hfi_small
  have hmeasure : (volume : Measure ℝ).real (Ioc y (y + 1)) = 1 := by
    simp
  have hlow' : Real.exp (-(θ * (y + 1))) * W y ≤
      ∫ z in Ioc y (y + 1), f z := by
    simpa [hmeasure] using hlow
  have hupp : (∫ z in Ioc y (y + 1), f z) ≤
      ∫ z in Ioi (0 : ℝ), f z :=
    setIntegral_mono_set hfi hf_nonneg (Filter.Eventually.of_forall (fun z hz => hsubset hz))
  have hLaplace := (hW.2.2.2.2 θ hθ hψ).2
  calc
    Real.exp (-(θ * (y + 1))) * W y ≤
        ∫ z in Ioc y (y + 1), f z := hlow'
    _ ≤ ∫ z in Ioi (0 : ℝ), f z := hupp
    _ = (X.ψ θ - q)⁻¹ := hLaplace
