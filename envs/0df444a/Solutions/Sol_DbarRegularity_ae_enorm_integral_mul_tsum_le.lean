-- Prove2me | solution 1 for DbarRegularity.ae_enorm_integral_mul_tsum_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:44:18.438125+00:00
-- url     : https://prove2.me/submissions/6aa34ef5-6f82-41cf-94d1-66c85cdd371b

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_DbarRegularity_ae_integrable_mul_sub_of_memLp_two_of_integrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence



namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- For `K ∈ L²(ℝ^d)` and integrable functions `bₖ` with pairwise disjoint supports and integrable
sum, almost everywhere `|K * ∑ₖ bₖ| ≤ ∑ₖ |K * bₖ|`. -/
theorem ae_enorm_integral_mul_tsum_le {d : ℕ} {K : EuclideanSpace ℝ (Fin d) → ℂ}
    (hK : MemLp K 2 volume) {ι : Type} [Countable ι] (b : ι → EuclideanSpace ℝ (Fin d) → ℂ)
    (hb : ∀ k, Integrable (b k) volume) (hdisj : ∀ x k l, b k x ≠ 0 → b l x ≠ 0 → k = l)
    (hB : Integrable (fun x => ∑' k, b k x) volume) :
    ∀ᵐ x, ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ ≤ ∑' k, ‖∫ y, K (x - y) * b k y‖ₑ := by
  have key : ∀ y, ∑' k, ‖b k y‖ₑ = ‖∑' k, b k y‖ₑ := by
    intro y
    by_cases h : ∃ k, b k y ≠ 0
    · obtain ⟨k, hk⟩ := h
      have hz : ∀ l, l ≠ k → b l y = 0 := by
        intro l hl
        by_contra h'
        exact hl (hdisj y l k h' hk)
      rw [tsum_eq_single k (fun l hl => by rw [hz l hl, enorm_zero]),
        tsum_eq_single k (fun l hl => hz l hl)]
    · push_neg at h
      simp [h]
  filter_upwards [ae_integrable_mul_sub_of_memLp_two_of_integrable hK hB] with x hx
  have hm : ∀ k, AEStronglyMeasurable (fun y => K (x - y) * b k y) volume := fun k =>
    (hK.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)).mul (hb k).1
  have hfin : ∑' k, ∫⁻ y, ‖K (x - y) * b k y‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun k => (hm k).enorm]
    simp_rw [enorm_mul, ENNReal.tsum_mul_left, key]
    have := hx.2
    rw [hasFiniteIntegral_iff_enorm] at this
    simpa only [enorm_mul] using this.ne
  have hmul : ∀ y, K (x - y) * ∑' k, b k y = ∑' k, K (x - y) * b k y := fun y =>
    tsum_mul_left.symm
  simp_rw [hmul]
  rw [integral_tsum hm hfin]
  exact enorm_tsum_le_tsum_enorm

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution {d : ℕ} {K : EuclideanSpace ℝ (Fin d) → ℂ}
    (hK : MemLp K 2 volume) {ι : Type} [Countable ι] (b : ι → EuclideanSpace ℝ (Fin d) → ℂ)
    (hb : ∀ k, Integrable (b k) volume) (hdisj : ∀ x k l, b k x ≠ 0 → b l x ≠ 0 → k = l)
    (hB : Integrable (fun x => ∑' k, b k x) volume) :
    ∀ᵐ x, ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ ≤ ∑' k, ‖∫ y, K (x - y) * b k y‖ₑ :=
  ae_enorm_integral_mul_tsum_le hK b hb hdisj hB
