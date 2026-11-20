-- Prove2me | solution 1 for ExploreFirst.Absolute.kl_monotone_right
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:01:12.885138+00:00
-- url     : https://prove2.me/submissions/d8bd5f97-0b85-4df0-a634-4148bd2ae427

import Mathlib
import Definitions.Def_ExploreFirst_Absolute_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

open ExploreFirst.FundIneq in
lemma ber_prob (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : IsProbabilityMeasure (bernoulliLaw a) := by
  constructor
  simp only [bernoulliLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]; simp

open ExploreFirst.FundIneq in
/-- Mixing two Bernoulli laws. -/
lemma ber_mix (p a b : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ENNReal.ofReal p • bernoulliLaw a + ENNReal.ofReal (1 - p) • bernoulliLaw b
      = bernoulliLaw (p * a + (1 - p) * b) := by
  have e1 : ENNReal.ofReal p * ENNReal.ofReal a + ENNReal.ofReal (1 - p) * ENNReal.ofReal b
      = ENNReal.ofReal (p * a + (1 - p) * b) := by
    rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (by positivity) (by nlinarith)]
  have e0 : ENNReal.ofReal p * ENNReal.ofReal (1 - a)
      + ENNReal.ofReal (1 - p) * ENNReal.ofReal (1 - b)
      = ENNReal.ofReal (1 - (p * a + (1 - p) * b)) := by
    rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
    congr 1; ring
  simp only [bernoulliLaw, smul_add, smul_smul]
  rw [add_add_add_comm, ← add_smul, ← add_smul, e1, e0]

theorem solution (p q q' : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hqq' : q ≤ q') (hq' : q' ≤ 1) :
    ExploreFirst.FundIneq.klBer p q ≤ ExploreFirst.FundIneq.klBer p q' := by
  open ExploreFirst.FundIneq in
  rcases eq_or_lt_of_le (hpq.trans hqq') with hpq' | hpq'
  · have h1 : p = q := le_antisymm hpq (hpq'.symm ▸ hqq')
    have h2 : q = q' := le_antisymm hqq' (hpq' ▸ h1 ▸ le_refl _)
    rw [← h2]
  · set t := (q - p) / (q' - p) with ht
    have hqp : 0 < q' - p := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hqp.le
    have ht1 : t ≤ 1 := (div_le_one hqp).mpr (by linarith)
    set b := p * (1 - t) with hb
    set a := b + t with ha
    have hp1 : p ≤ 1 := by linarith
    have hb0 : 0 ≤ b := mul_nonneg hp (by linarith)
    have hb1 : b ≤ 1 := by nlinarith
    have ha0 : 0 ≤ a := by linarith
    have ha1 : a ≤ 1 := by nlinarith
    haveI := ber_prob a ha0 ha1
    haveI := ber_prob b hb0 hb1
    let κ : ProbabilityTheory.Kernel ℝ ℝ :=
      ProbabilityTheory.Kernel.piecewise (measurableSet_singleton (1 : ℝ))
        (ProbabilityTheory.Kernel.const ℝ (bernoulliLaw a))
        (ProbabilityTheory.Kernel.const ℝ (bernoulliLaw b))
    haveI : IsMarkovKernel κ := by
      unfold κ; infer_instance
    have hκ1 : κ 1 = bernoulliLaw a := by
      simp [κ, ProbabilityTheory.Kernel.piecewise_apply]
    have hκ0 : κ 0 = bernoulliLaw b := by
      simp [κ, ProbabilityTheory.Kernel.piecewise_apply]
    have hcomp : ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
        κ ∘ₘ bernoulliLaw c = bernoulliLaw (c * a + (1 - c) * b) := by
      intro c hc0 hc1
      rw [bernoulliLaw, Measure.comp_add, Measure.comp_smul, Measure.comp_smul,
        Measure.dirac_bind (κ.measurable), Measure.dirac_bind (κ.measurable), hκ1, hκ0]
      exact ber_mix c a b hc0 hc1 ha0 ha1 hb0 hb1
    have hP : p * a + (1 - p) * b = p := by
      simp only [ha, hb]; ring
    have hQ : q' * a + (1 - q') * b = q := by
      simp only [ha, hb, ht]; field_simp; ring
    haveI := ber_prob p hp hp1
    haveI := ber_prob q' (by linarith) hq'
    have h := klDiv_comp_right_le (bernoulliLaw p) (bernoulliLaw q') κ
    rw [hcomp p hp hp1, hcomp q' (by linarith) hq', hP, hQ] at h
    exact h
