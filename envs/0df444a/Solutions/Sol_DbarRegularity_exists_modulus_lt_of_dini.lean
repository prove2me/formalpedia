-- Prove2me | solution 1 for DbarRegularity.exists_modulus_lt_of_dini
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T19:21:32.4202+00:00
-- url     : https://prove2.me/submissions/43500e2e-6ff6-4d87-8d91-b0d22ab927e8

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal

/-- If the modulus of continuity `w(δ) = sup {|Ω(x) - Ω(x')| : |x| = |x'| = 1, |x - x'| ≤ δ}` of a
function `Ω` on the unit sphere of `ℝ^d` satisfies `∫₀¹ w(δ) / δ dδ < ∞`, then `w(δ)` becomes
arbitrarily small for small `δ > 0`. -/
theorem exists_modulus_lt_of_dini {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d))
        (_ : ‖x‖ = 1) (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) < ENNReal.ofReal ε := by
  by_contra hcon
  push_neg at hcon
  -- `∫₀¹ dδ / δ = ∞`
  have hnot : ¬ IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo 0 1) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]; norm_num
  have hinf : ∫⁻ x in Ioo (0 : ℝ) 1, ‖x ^ (-1 : ℝ)‖ₑ = ⊤ := by
    by_contra h
    exact hnot ⟨(measurable_id.pow_const _).aestronglyMeasurable, lt_top_iff_ne_top.2 h⟩
  have hinf' : ∫⁻ x in Ioc (0 : ℝ) 1, (ENNReal.ofReal x)⁻¹ = ⊤ := by
    refine eq_top_iff.2 (hinf.symm.le.trans ?_)
    calc ∫⁻ x in Ioo (0 : ℝ) 1, ‖x ^ (-1 : ℝ)‖ₑ
        = ∫⁻ x in Ioo (0 : ℝ) 1, (ENNReal.ofReal x)⁻¹ := by
          refine setLIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
          rw [Real.rpow_neg_one, ← ofReal_norm_eq_enorm, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hx.1), ENNReal.ofReal_inv_of_pos hx.1]
      _ ≤ _ := lintegral_mono_set Ioo_subset_Ioc_self
  have : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal ε * (ENNReal.ofReal x)⁻¹ = ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hinf',
      ENNReal.mul_top (by simpa using hε)]
  refine hdini.ne (eq_top_iff.2 (this.symm.le.trans (setLIntegral_mono' measurableSet_Ioc
    (fun δ hδ => ?_))))
  rw [div_eq_mul_inv]
  exact mul_le_mul' (hcon δ hδ.1) le_rfl

end DbarRegularity

open DbarRegularity

open MeasureTheory Set
open scoped ENNReal

theorem solution {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d))
        (_ : ‖x‖ = 1) (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) < ENNReal.ofReal ε :=
  exists_modulus_lt_of_dini Ω hdini ε hε
