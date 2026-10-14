-- Prove2me | solution 1 for DbarRegularity.lintegral_Ioi_indicator_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:03:52.941837+00:00
-- url     : https://prove2.me/submissions/8a058f40-1b13-4a92-bb4e-05541b443a34

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic



namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal NNReal

/-- `∫_{0 < t, t < a} q t^(q-1) dt = a^q` for every `a ∈ [0, ∞]` and `q > 0`. -/
lemma lintegral_Ioi_indicator_rpow (a : ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < a}.indicator
      (fun t => ENNReal.ofReal (q * t ^ (q - 1))) t = a ^ q := by
  have hS : ∀ b : ℝ≥0∞, MeasurableSet {t : ℝ | ENNReal.ofReal t < b} := fun b =>
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  -- finite case
  have fin : ∀ s : ℝ, 0 ≤ s →
      ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < ENNReal.ofReal s}.indicator
        (fun t => ENNReal.ofReal (q * t ^ (q - 1))) t = ENNReal.ofReal (s ^ q) := by
    intro s hs
    rw [lintegral_indicator (hS _), Measure.restrict_restrict (hS _)]
    have hset : {t : ℝ | ENNReal.ofReal t < ENNReal.ofReal s} ∩ Ioi 0 = Ioo 0 s := by
      ext t
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_Ioo, ENNReal.ofReal_lt_ofReal_iff']
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h3, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1.trans h2⟩, h1⟩
    rw [hset]
    have hint : IntegrableOn (fun t : ℝ => q * t ^ (q - 1)) (Ioo 0 s) := by
      have := ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := s)
        (by linarith : (-1 : ℝ) < q - 1)).const_mul q).1
      exact this.mono_set Ioo_subset_Ioc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint]
    · congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs,
        intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
      rw [sub_add_cancel, Real.zero_rpow hq.ne', sub_zero]
      field_simp
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => ?_)
      exact mul_nonneg hq.le (Real.rpow_nonneg ht.1.le _)
  rcases eq_or_ne a ⊤ with rfl | ha
  · rw [ENNReal.top_rpow_of_pos hq]
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    have hr : (0 : ℝ) ≤ (r : ℝ) ^ q⁻¹ := Real.rpow_nonneg r.2 _
    calc (r : ℝ≥0∞) = ENNReal.ofReal (((r : ℝ) ^ q⁻¹) ^ q) := by
          have e : ((r : ℝ) ^ q⁻¹) ^ q = (r : ℝ) := Real.rpow_inv_rpow r.2 hq.ne'
          rw [e, ENNReal.ofReal_coe_nnreal]
      _ = _ := (fin _ hr).symm
      _ ≤ _ := by
          refine lintegral_mono fun t => indicator_le_indicator_of_subset ?_ (fun _ => bot_le) t
          intro t _
          exact ENNReal.ofReal_lt_top
  · have h := fin a.toReal ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_toReal ha] at h
    rw [h, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hq.le, ENNReal.ofReal_toReal ha]

end DbarRegularity

open DbarRegularity

open MeasureTheory Set
open scoped ENNReal

theorem solution (a : ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t < a}.indicator
      (fun t => ENNReal.ofReal (q * t ^ (q - 1))) t = a ^ q :=
  lintegral_Ioi_indicator_rpow a hq
