-- Prove2me | solution 1 for CauchyRiemannIndex.memLp_of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T11:25:27.281374+00:00
-- url     : https://prove2.me/submissions/f7762c52-ff28-4ef4-a321-195b1f45d1fc

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

/-- Interpolation of integrability exponents. -/
lemma ipk_interp {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {f : α → E} {p q r : ℝ≥0∞} (hp0 : p ≠ 0) (hpq : p ≤ r) (hrq : r ≤ q) (hqt : q ≠ ⊤)
    (hfp : MemLp f p μ) (hfq : MemLp f q μ) : MemLp f r μ := by
  have hr0 : r ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hp0) hpq).ne'
  have hrt : r ≠ ⊤ := ne_top_of_le_ne_top hqt hrq
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top hrt hpq
  have hq0 : q ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hr0) hrq).ne'
  refine ⟨hfp.1, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hr0 hrt]
  have Ip := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt).1 hfp.2
  have Iq := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hqt).1 hfq.2
  have hpr : p.toReal ≤ r.toReal := ENNReal.toReal_mono hrt hpq
  have hrq' : r.toReal ≤ q.toReal := ENNReal.toReal_mono hqt hrq
  have hpt0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hpw : ∀ x, ‖f x‖ₑ ^ r.toReal ≤ ‖f x‖ₑ ^ p.toReal + ‖f x‖ₑ ^ q.toReal := by
    intro x
    rcases le_total ‖f x‖ₑ 1 with h | h
    · exact (ENNReal.rpow_le_rpow_of_exponent_ge h hpr).trans le_self_add
    · exact (ENNReal.rpow_le_rpow_of_exponent_le h hrq').trans le_add_self
  calc ∫⁻ x, ‖f x‖ₑ ^ r.toReal ∂μ
      ≤ ∫⁻ x, (‖f x‖ₑ ^ p.toReal + ‖f x‖ₑ ^ q.toReal) ∂μ := lintegral_mono hpw
    _ = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ + ∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ :=
        lintegral_add_left' (hfp.1.enorm.pow_const _) _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨Ip, Iq⟩

end CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

theorem solution {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} {p q r : ℝ≥0∞} (hp0 : p ≠ 0) (hpr : p ≤ r) (hrq : r ≤ q)
    (hqt : q ≠ ⊤) (hfp : MemLp f p μ) (hfq : MemLp f q μ) : MemLp f r μ :=
  CauchyRiemannIndex.ipk_interp hp0 hpr hrq hqt hfp hfq
