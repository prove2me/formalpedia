-- Prove2me | solution 1 for DbarRegularity.ae_integrable_mul_sub_of_memLp_two_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:25:37.961465+00:00
-- url     : https://prove2.me/submissions/1760cc01-ee48-4372-933e-2a7ef3118813

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_DbarRegularity_lintegral_sq_lintegral_mul_le
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov



namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- For `K ∈ L²(ℝ^d)` and `f ∈ L¹(ℝ^d)`, the integrand `y ↦ K(x - y) f(y)` is integrable for almost
every `x`. -/
theorem ae_integrable_mul_sub_of_memLp_two_of_integrable {d : ℕ}
    {K f : EuclideanSpace ℝ (Fin d) → ℂ} (hK : MemLp K 2 volume) (hf : Integrable f volume) :
    ∀ᵐ x, Integrable (fun y => K (x - y) * f y) volume := by
  have H := lintegral_sq_lintegral_mul_le K f hK.1 hf.1
  have hK2 : ∫⁻ x, ‖K x‖ₑ ^ 2 < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (two_ne_zero) ENNReal.ofNat_ne_top hK.2
    simpa [ENNReal.toReal_ofNat] using this
  have hf1 : ∫⁻ y, ‖f y‖ₑ < ⊤ := hf.2
  have hfin : ∫⁻ x, (∫⁻ y, ‖K (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ≠ ⊤ :=
    (H.trans_lt (ENNReal.mul_lt_top hK2 (ENNReal.pow_lt_top hf1))).ne
  have hm : AEMeasurable (fun x : EuclideanSpace ℝ (Fin d) =>
      (∫⁻ y, ‖K (x - y)‖ₑ * ‖f y‖ₑ) ^ 2) volume := by
    have h1 : AEMeasurable (Function.uncurry fun (x y : EuclideanSpace ℝ (Fin d)) =>
        ‖K (x - y)‖ₑ * ‖f y‖ₑ) (volume.prod volume) :=
      (hK.1.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)).mul
        (hf.1.enorm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    exact h1.lintegral_prod_right'.pow_const 2
  filter_upwards [ae_lt_top' hm hfin] with x hx
  refine ⟨(hK.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)).mul hf.1,
    ?_⟩
  have : ∫⁻ y, ‖K (x - y)‖ₑ * ‖f y‖ₑ < ⊤ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h] at hx; simp at hx
  simpa [HasFiniteIntegral, enorm_mul] using this

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution {d : ℕ}
    {K f : EuclideanSpace ℝ (Fin d) → ℂ} (hK : MemLp K 2 volume) (hf : Integrable f volume) :
    ∀ᵐ x, Integrable (fun y => K (x - y) * f y) volume :=
  ae_integrable_mul_sub_of_memLp_two_of_integrable hK hf
