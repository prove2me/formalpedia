-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing_parts_final
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:41:34.410985+00:00
-- url     : https://prove2.me/submissions/b626b3e2-a229-490e-9fcf-7efca9feff6e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Almost-everywhere q-harmonicity of the scale function from agreement of
the weighted transforms of the two parts of the generator residual. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (b : ℝ)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hpart : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
        max (X.generator W x - q * W x) 0) (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
        max (-(X.generator W x - q * W x)) 0) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
        max (X.generator W x - q * W x) 0) =
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
        max (-(X.generator W x - q * W x)) 0)) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo 0 a)),
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
  have hRpnonneg : ∀ x : ℝ, 0 < x → 0 ≤ max (R x) 0 := by
    intro x hx
    exact le_max_right _ _
  have hRmnonneg : ∀ x : ℝ, 0 < x → 0 ≤ max (-(R x)) 0 := by
    intro x hx
    exact le_max_right _ _
  -- The two parts agree pointwise on the positive half-line, by the uniqueness
  -- of the Laplace transform of nonnegative continuous functions.
  have hzero : ∀ x : ℝ, 0 < x →
      max (X.generator W x - q * W x) 0 = max (-(X.generator W x - q * W x)) 0 := by
    intro x hx
    exact (continuousOn_Ioi_eq_of_laplace_eq
      (fun x : ℝ => max (X.generator W x - q * W x) 0)
      (fun x : ℝ => max (-(X.generator W x - q * W x)) 0) b
      (by simpa [R] using hRpcont) (by simpa [R] using hRmcont)
      (by simpa [R] using hRpnonneg) (by simpa [R] using hRmnonneg)
      -- The hypothesis of the uniqueness theorem is stated with the residual
      -- expanded, so the hypothesis of this theorem has exactly that shape and
      -- is used directly.
      hpart) x hx
  -- Equality of the two parts gives vanishing of the residual.
  have hRzero (x : ℝ) (hx : 0 < x) : R x = 0 := by
    have h := hzero x hx
    by_cases hr : X.generator W x - q * W x ≤ 0
    · have hneg : 0 ≤ -(X.generator W x - q * W x) := by simpa using neg_nonneg.mpr hr
      have hzero1 : max (X.generator W x - q * W x) 0 = 0 :=
        max_eq_right hr
      have hzero2 : max (-(X.generator W x - q * W x)) 0 =
          -(X.generator W x - q * W x) := max_eq_left hneg
      rw [hzero1, hzero2] at h
      have hx0 : X.generator W x - q * W x = 0 := by linarith
      simpa [R] using hx0
    · have hpos : 0 ≤ X.generator W x - q * W x := le_of_not_ge hr
      have hzero1 : max (X.generator W x - q * W x) 0 =
          X.generator W x - q * W x := max_eq_left hpos
      have hzero2 : max (-(X.generator W x - q * W x)) 0 = 0 :=
        max_eq_right (by simpa using neg_nonpos.mpr hpos)
      rw [hzero1, hzero2] at h
      have hx0 : X.generator W x - q * W x = 0 := by linarith
      simpa [R] using hx0
  -- The residual vanishes at every point of the positive half-line, so in
  -- particular almost everywhere on `(0, a)`.
  have hmem : ∀ x : ℝ, x ∈ Ioo 0 a → R x = 0 := by
    intro x hx
    exact hRzero x hx.1
  have hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo 0 a)), R x = 0 := by
    exact ae_restrict_of_forall_mem measurableSet_Ioo hmem
  have hae' : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by
    filter_upwards [hae] with x hx
    simpa [R] using hx
  exact hae'
