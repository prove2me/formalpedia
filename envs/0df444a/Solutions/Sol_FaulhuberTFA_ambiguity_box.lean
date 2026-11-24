-- Prove2me | solution 1 for FaulhuberTFA.ambiguity_box
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:33:00.867584+00:00
-- url     : https://prove2.me/submissions/47d4bf3f-d468-4d85-9630-fb492e336566

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

set_option autoImplicit false

namespace FaulhuberTFA

lemma ex_int1 (F : ℝ → ℂ) : ∫ t : Rd 1, F (t 0) = ∫ r : ℝ, F r := by
  rw [← (PiLp.volume_preserving_toLp (Fin 1)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  exact (volume_preserving_funUnique (Fin 1) ℝ).integral_comp' F

lemma ex_box_pt (a r : ℝ) :
    ((if |r + 1 / 2 * a| ≤ 1 / 2 then (1 : ℂ) else 0) *
      starRingEnd ℂ (if |r - 1 / 2 * a| ≤ 1 / 2 then (1 : ℂ) else 0)) =
      Set.indicator (Set.Icc (-((1 - |a|) / 2)) ((1 - |a|) / 2)) (fun _ => (1 : ℂ)) r := by
  have key : (|r + 1 / 2 * a| ≤ 1 / 2 ∧ |r - 1 / 2 * a| ≤ 1 / 2) ↔
      r ∈ Set.Icc (-((1 - |a|) / 2)) ((1 - |a|) / 2) := by
    simp only [Set.mem_Icc, abs_le]
    rcases le_total 0 a with h | h
    · rw [abs_of_nonneg h]; constructor <;> intro h' <;> constructor <;> (try constructor) <;>
        linarith [h'.1, h'.2]
    · rw [abs_of_nonpos h]; constructor <;> intro h' <;> constructor <;> (try constructor) <;>
        linarith [h'.1, h'.2]
  by_cases hm : r ∈ Set.Icc (-((1 - |a|) / 2)) ((1 - |a|) / 2)
  · rw [Set.indicator_of_mem hm]
    obtain ⟨h1, h2⟩ := key.2 hm
    rw [if_pos h1, if_pos h2]; simp
  · rw [Set.indicator_of_notMem hm]
    by_cases h1 : |r + 1 / 2 * a| ≤ 1 / 2
    · have h2 : ¬ |r - 1 / 2 * a| ≤ 1 / 2 := fun h2 => hm (key.1 ⟨h1, h2⟩)
      rw [if_neg h2]; simp
    · rw [if_neg h1]; simp

lemma ex_box_amb (x ω : Rd 1) :
    ambiguity box0 x ω = ∫ r in Set.Icc (-((1 - |x 0|) / 2)) ((1 - |x 0|) / 2),
      cexp ((-2 * Real.pi * ω 0 * I : ℂ) * r) := by
  unfold ambiguity crossAmbiguity box0
  have hpt : ∀ t : Rd 1, ((if |(t + (1 / 2 : ℝ) • x) 0| ≤ 1 / 2 then (1 : ℂ) else 0) *
      starRingEnd ℂ (if |(t - (1 / 2 : ℝ) • x) 0| ≤ 1 / 2 then (1 : ℂ) else 0) *
      ePhase (-⟪ω, t⟫_ℝ)) =
      (fun r : ℝ => Set.indicator (Set.Icc (-((1 - |x 0|) / 2)) ((1 - |x 0|) / 2))
        (fun r : ℝ => cexp ((-2 * Real.pi * ω 0 * I : ℂ) * r)) r) (t 0) := by
    intro t
    have e1 : (t + (1 / 2 : ℝ) • x) 0 = t 0 + 1 / 2 * x 0 := by simp
    have e2 : (t - (1 / 2 : ℝ) • x) 0 = t 0 - 1 / 2 * x 0 := by simp
    rw [e1, e2, ex_box_pt]
    simp only [Set.indicator_apply]
    split_ifs
    · rw [one_mul, ePhase]; congr 1
      simp [PiLp.inner_apply]; ring
    · simp
  simp_rw [hpt]
  rw [ex_int1, integral_indicator measurableSet_Icc]

end FaulhuberTFA

open FaulhuberTFA in
theorem solution (x ω : Rd 1) :
    ambiguity box0 x ω =
      if |x 0| ≤ 1 then
        (if ω 0 = 0 then ((1 - |x 0| : ℝ) : ℂ)
         else ((Real.sin (Real.pi * ω 0 * (1 - |x 0|)) / (Real.pi * ω 0) : ℝ) : ℂ))
      else 0 := by
  rw [ex_box_amb]
  set c : ℝ := (1 - |x 0|) / 2 with hc
  split_ifs with ha hw
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    simp only [hw]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, Complex.real_smul]
    rw [hc]; push_cast; ring
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have hk : (-2 * Real.pi * ω 0 * I : ℂ) ≠ 0 := by
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have : (ω 0 : ℂ) ≠ 0 := by exact_mod_cast hw
      simp_all
    rw [integral_exp_mul_complex hk]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hw' : (ω 0 : ℂ) ≠ 0 := by exact_mod_cast hw
    have hs : Real.pi * ω 0 * (1 - |x 0|) = 2 * Real.pi * ω 0 * c := by rw [hc]; ring
    rw [hs]
    push_cast
    rw [Complex.sin]
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
  · have : Set.Icc (-c) c = ∅ := Set.Icc_eq_empty (by rw [hc]; linarith [not_le.mp ha])
    rw [this, Measure.restrict_empty, integral_zero_measure]
