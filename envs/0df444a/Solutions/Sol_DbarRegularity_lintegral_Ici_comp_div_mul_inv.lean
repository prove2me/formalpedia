-- Prove2me | solution 1 for DbarRegularity.lintegral_Ici_comp_div_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T19:32:23.940319+00:00
-- url     : https://prove2.me/submissions/db90ae32-bee1-4e82-85d5-1aa7139da278

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inv



namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal

/-- For `c > 0` and any `w : ℝ → [0, ∞]`:
`∫_{r ≥ c} w(c / r) dr / r = ∫_{0 < δ ≤ 1} w(δ) dδ / δ`. -/
theorem lintegral_Ici_comp_div_mul_inv {c : ℝ} (hc : 0 < c) (w : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ici c, w (c / r) * (ENNReal.ofReal r)⁻¹ =
      ∫⁻ δ in Ioc (0 : ℝ) 1, w δ * (ENNReal.ofReal δ)⁻¹ := by
  set f : ℝ → ℝ := fun δ => c / δ with hf
  have himg : f '' Ioc (0 : ℝ) 1 = Ici c := by
    ext r
    simp only [mem_image, mem_Ioc, mem_Ici, hf]
    constructor
    · rintro ⟨δ, ⟨h0, h1⟩, rfl⟩
      rw [le_div_iff₀ h0]; nlinarith
    · intro hr
      have hr0 : 0 < r := hc.trans_le hr
      refine ⟨c / r, ⟨div_pos hc hr0, (div_le_one hr0).2 hr⟩, ?_⟩
      field_simp
  have hderiv : ∀ δ ∈ Ioc (0 : ℝ) 1, HasDerivWithinAt f (-(c / δ ^ 2)) (Ioc 0 1) δ := by
    intro δ hδ
    have := ((hasDerivAt_inv hδ.1.ne').const_mul c).hasDerivWithinAt (s := Ioc (0 : ℝ) 1)
    have h : f = fun y => c * y⁻¹ := by funext y; simp [hf, div_eq_mul_inv]
    rw [show -(c / δ ^ 2) = c * -(δ ^ 2)⁻¹ by ring, h]
    exact this
  have hinj : InjOn f (Ioc (0 : ℝ) 1) := by
    intro a ha b hb hab
    simp only [hf] at hab
    rw [div_eq_div_iff ha.1.ne' hb.1.ne'] at hab
    have := mul_left_cancel₀ hc.ne' hab
    exact this.symm
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hderiv hinj]
  refine setLIntegral_congr_fun measurableSet_Ioc (fun δ hδ => ?_)
  have hδ0 : 0 < δ := hδ.1
  have hcd : 0 < c / δ := div_pos hc hδ0
  simp only [hf]
  rw [div_div_cancel₀ hc.ne', abs_neg, abs_of_pos (by positivity),
    show c / δ ^ 2 = c / δ * δ⁻¹ by field_simp, ENNReal.ofReal_mul hcd.le,
    ENNReal.ofReal_inv_of_pos hδ0]
  have hne : ENNReal.ofReal (c / δ) ≠ 0 := by simpa using hcd
  calc ENNReal.ofReal (c / δ) * (ENNReal.ofReal δ)⁻¹ * (w δ * (ENNReal.ofReal (c / δ))⁻¹)
      = w δ * (ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal (c / δ) * (ENNReal.ofReal (c / δ))⁻¹) := by
        ring
    _ = w δ * (ENNReal.ofReal δ)⁻¹ := by
        rw [ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top, mul_one]

end DbarRegularity

open DbarRegularity

open MeasureTheory Set
open scoped ENNReal

theorem solution {c : ℝ} (hc : 0 < c) (w : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ici c, w (c / r) * (ENNReal.ofReal r)⁻¹ =
      ∫⁻ δ in Ioc (0 : ℝ) 1, w δ * (ENNReal.ofReal δ)⁻¹ :=
  lintegral_Ici_comp_div_mul_inv hc w
