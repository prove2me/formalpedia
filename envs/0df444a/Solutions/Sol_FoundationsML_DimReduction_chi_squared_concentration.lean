-- Prove2me | solution 1 for FoundationsML.DimReduction.chi_squared_concentration
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T23:21:15.074312+00:00
-- url     : https://prove2.me/submissions/217f0a22-886f-4a9d-870f-23465437dd91

import Mathlib
import Definitions.Def_FoundationsML_DimReduction_IsChiSquaredMGF

open MeasureTheory
open MeasureTheory ProbabilityTheory

namespace FoundationsML.DimReduction

lemma chi_log_upper {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    Real.log (1 + ε) ≤ ε - ε ^ 2 / 2 + ε ^ 3 / 2 := by
  have hx : |(-ε)| < 1 := by rw [abs_neg, abs_of_pos h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 6
  rw [abs_neg, abs_of_pos h0, sub_neg_eq_add] at h
  simp [Finset.sum_range_succ] at h
  have h' := (abs_le.mp h).2
  have e3 : (-ε) ^ 3 = -ε ^ 3 := by ring
  have e4 : (-ε) ^ 4 = ε ^ 4 := by ring
  have e5 : (-ε) ^ 5 = -ε ^ 5 := by ring
  have e6 : (-ε) ^ 6 = ε ^ 6 := by ring
  rw [e3, e4, e5, e6] at h'
  norm_num at h'
  have hd : ε ^ 7 / (1 - ε) ≤ 2 * ε ^ 7 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [mul_pos (pow_pos h0 7) h0]
  have p : ε ^ 7 ≤ ε ^ 3 / 16 := by
    have : ε ^ 4 ≤ (1/2) ^ 4 := pow_le_pow_left₀ h0.le h1.le 4
    nlinarith [pow_pos h0 3]
  have q : ε ^ 5 ≤ ε ^ 3 / 4 := by
    have : ε ^ 2 ≤ (1/2) ^ 2 := pow_le_pow_left₀ h0.le h1.le 2
    nlinarith [pow_pos h0 3]
  nlinarith [pow_pos h0 3, pow_pos h0 4, pow_pos h0 6]

lemma chi_log_lower {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    Real.log (1 - ε) ≤ -ε - ε ^ 2 / 2 + ε ^ 3 / 2 := by
  have hx : |ε| < 1 := by rw [abs_of_pos h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  rw [abs_of_pos h0] at h
  simp [Finset.sum_range_succ] at h
  have h' := (abs_le.mp h).2
  norm_num at h'
  have hd : ε ^ 5 / (1 - ε) ≤ 2 * ε ^ 5 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [mul_pos (pow_pos h0 5) h0]
  nlinarith [pow_pos h0 3, pow_pos h0 4, pow_pos h0 5, mul_pos (pow_pos h0 3) h0,
    mul_pos (pow_pos h0 3) (pow_pos h0 2)]

lemma chi_integrable {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} {Q : Ω → ℝ} {k : ℕ}
    (hQ : IsChiSquaredMGF Prob Q k) {lam : ℝ} (hl : lam < 1 / 2) :
    Integrable (fun ω => Real.exp (lam * Q ω)) Prob := by
  by_contra hni
  have := hQ lam hl
  rw [integral_undef hni] at this
  have hpos : 0 < (1 - 2 * lam) ^ (-(k : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  linarith

theorem chi_main {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    [IsProbabilityMeasure Prob] (Q : Ω → ℝ) (k : ℕ) (hQ : IsChiSquaredMGF Prob Q k)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    1 - 2 * Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) ≤
      Prob.real {ω | (1 - ε) * (k : ℝ) ≤ Q ω ∧ Q ω ≤ (1 + ε) * (k : ℝ)} := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set B := Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) with hB
  -- upper tail
  set t := ε / (2 * (1 + ε)) with ht
  have ht0 : 0 ≤ t := by positivity
  have htl : t < 1 / 2 := by rw [ht, div_lt_iff₀ (by positivity)]; linarith
  have hup := measure_ge_le_exp_mul_mgf (μ := Prob) (X := Q) ((1 + ε) * k) ht0
    (chi_integrable hQ htl)
  have hmgf1 : mgf Q Prob t = (1 - 2 * t) ^ (-(k : ℝ) / 2) := hQ t htl
  have h12t : 1 - 2 * t = (1 + ε)⁻¹ := by rw [ht]; field_simp <;> ring
  have hupB : Prob.real {ω | (1 + ε) * k ≤ Q ω} ≤ B := by
    refine hup.trans (le_of_eq_of_le (by rw [hmgf1]) ?_)
    rw [h12t, Real.rpow_def_of_pos (by positivity), Real.log_inv, ← Real.exp_add, hB,
      Real.exp_le_exp]
    have hl := chi_log_upper hε0 hε1
    have : -t * ((1 + ε) * k) = -(ε * k / 2) := by rw [ht]; field_simp <;> ring
    rw [this]
    nlinarith [mul_nonneg hk (by nlinarith : (0:ℝ) ≤ ε - ε ^ 2 / 2 + ε ^ 3 / 2 - Real.log (1 + ε))]
  -- lower tail
  set s := -(ε / (2 * (1 - ε))) with hs
  have h1e' : (0 : ℝ) < 1 - ε := by linarith
  have hs0 : s ≤ 0 := by rw [hs]; exact neg_nonpos.mpr (by positivity)
  have hsl : s < 1 / 2 := by linarith
  have hlo := measure_le_le_exp_mul_mgf (μ := Prob) (X := Q) ((1 - ε) * k) hs0
    (chi_integrable hQ hsl)
  have hmgf2 : mgf Q Prob s = (1 - 2 * s) ^ (-(k : ℝ) / 2) := hQ s hsl
  have h1e : (0 : ℝ) < 1 - ε := by linarith
  have h12s : 1 - 2 * s = (1 - ε)⁻¹ := by rw [hs]; field_simp <;> ring
  have hloB : Prob.real {ω | Q ω ≤ (1 - ε) * k} ≤ B := by
    refine hlo.trans (le_of_eq_of_le (by rw [hmgf2]) ?_)
    rw [h12s, Real.rpow_def_of_pos (by positivity), Real.log_inv, ← Real.exp_add, hB,
      Real.exp_le_exp]
    have hl := chi_log_lower hε0 hε1
    have : -s * ((1 - ε) * k) = ε * k / 2 := by rw [hs]; field_simp
    rw [this]
    nlinarith [mul_nonneg hk (by nlinarith : (0:ℝ) ≤ -ε - ε ^ 2 / 2 + ε ^ 3 / 2 - Real.log (1 - ε))]
  -- combine
  set E := {ω | (1 - ε) * (k : ℝ) ≤ Q ω ∧ Q ω ≤ (1 + ε) * (k : ℝ)}
  have hsub : Eᶜ ⊆ {ω | (1 + ε) * k ≤ Q ω} ∪ {ω | Q ω ≤ (1 - ε) * k} := by
    intro ω hω
    simp only [E, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hω
    rcases hω with h | h
    · right; exact h.le
    · left; exact h.le
  have h1 : (1 : ℝ) ≤ Prob.real E + Prob.real Eᶜ := by
    have := measureReal_union_le (μ := Prob) E Eᶜ
    rwa [Set.union_compl_self, probReal_univ] at this
  have h2 := (measureReal_mono (μ := Prob) hsub).trans (measureReal_union_le _ _)
  linarith

end FoundationsML.DimReduction

open FoundationsML.DimReduction

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    [IsProbabilityMeasure Prob] (Q : Ω → ℝ) (k : ℕ) (hQ : IsChiSquaredMGF Prob Q k)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    1 - 2 * Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) ≤
      Prob.real {ω | (1 - ε) * (k : ℝ) ≤ Q ω ∧ Q ω ≤ (1 + ε) * (k : ℝ)} := by
  exact chi_main Prob Q k hQ ε hε0 hε1
