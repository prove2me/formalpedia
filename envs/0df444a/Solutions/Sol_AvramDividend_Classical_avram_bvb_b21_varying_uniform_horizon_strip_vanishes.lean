-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_varying_uniform_horizon_strip_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:55:22.104134+00:00
-- url     : https://prove2.me/submissions/9918d46d-b813-4471-a597-7e83c9d2c023

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

/-- Uniformly bounded changing kernels contribute no terminal-grid strip. -/
theorem solution (T B : ℝ) (hT : 0 < T) (hB : 0 ≤ B)
    (f : ℕ → ℝ → ℝ)
    (hf : ∀ n, IntegrableOn (f n) (Icc (0 : ℝ) T) volume)
    (hbound : ∀ n t, t ∈ Icc (0 : ℝ) T →
      0 ≤ f n t ∧ f n t ≤ B) :
    Tendsto
      (fun n : ℕ => ∫ t in Icc (T - T / ((n : ℝ) + 2)) T, f n t)
      atTop (𝓝 0) := by
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  have hδpos (n : ℕ) : 0 ≤ δ n :=
    div_nonneg hT.le (by positivity)
  have hδle (n : ℕ) : δ n ≤ T :=
    div_le_self hT.le (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hsub (n : ℕ) : Icc (T - δ n) T ⊆ Icc (0 : ℝ) T := by
    intro t ht
    exact ⟨le_trans (sub_nonneg.mpr (hδle n)) ht.1, ht.2⟩
  have hnonneg (n : ℕ) :
      0 ≤ ∫ t in Icc (T - δ n) T, f n t := by
    exact setIntegral_nonneg measurableSet_Icc
      (fun t ht => (hbound n t (hsub n ht)).1)
  have hupper (n : ℕ) :
      (∫ t in Icc (T - δ n) T, f n t) ≤ B * δ n := by
    calc
      _ ≤ ∫ t in Icc (T - δ n) T, B := by
        apply setIntegral_mono_on ((hf n).mono_set (hsub n))
          (integrableOn_const (s := Icc (T - δ n) T) (μ := volume)
            (by simp [Real.volume_Icc])) measurableSet_Icc
        intro t ht
        exact (hbound n t (hsub n ht)).2
      _ = B * δ n := by
        simp only [integral_const, MeasureTheory.Measure.real,
          MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        simp [ENNReal.toReal_ofReal, hδpos n, smul_eq_mul] <;> ring
  have hδtend : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, Nat.cast_add, Nat.cast_ofNat] using
      ((tendsto_add_atTop_iff_nat 2).2
        (tendsto_const_div_atTop_nhds_zero_nat T))
  exact squeeze_zero hnonneg hupper (by
    simpa using (tendsto_const_nhds.mul hδtend))
