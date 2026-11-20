-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_uniform_true_stop_preterminal_HJB_Q_allgrids_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:56:57.510174+00:00
-- url     : https://prove2.me/submissions/85856b77-c949-4233-8d7c-5635443c3daa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_allphysical_grids_HJB_and_rightpayment_Q_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (u v δ : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (huv : u + δ < v) (hvCap : v < C.toReal)
    (T : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let A : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      (Finset.range (k + 1)).image
        (fun i : ℕ => ρ ω * ((i : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
    ∀ k : ℕ,
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        ((if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
          (if Y p ∈ Icc (u + δ) v then
            X.generator w (Y p) - q * w (Y p) else 0))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let B : Ω → ℝ := fun ω =>
      ∫ t : ℝ≥0, if t ≤ ρ ω then R (t, ω) else 0 ∂μT
    let Q : Ω → ℝ := fun ω => B ω +
      ∑ t ∈ A k ω, Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) -
          (w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω))))
    ∀ ω, Q ω ≤ 0 := by
  intro A
  have hPre : ∀ k ω t, t ∈ A k ω →
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω := by
    intro k ω t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    have hifin : i < k + 1 := Finset.mem_range.mp hi
    by_cases hzero : ρ ω = 0
    · left
      simp [hzero]
    · right
      have hkpos : (0 : ℝ≥0) < (k + 1 : ℕ) := by
        exact_mod_cast (Nat.zero_lt_succ k)
      have hfrac : ((i : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)) < 1 := by
        apply (div_lt_iff₀ hkpos).2
        simpa only [one_mul] using
          (show (i : ℝ≥0) < ((k + 1 : ℕ) : ℝ≥0) from by
            exact_mod_cast hifin)
      have hρpos : (0 : ℝ≥0) < ρ ω := pos_iff_ne_zero.mpr hzero
      have hlt : ρ ω * ((i : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)) < ρ ω := by
        exact (mul_lt_mul_of_pos_left hfrac hρpos).trans_eq (mul_one _)
      exact (ENNReal.coe_lt_coe.mpr hlt).trans_le (hρruin ω)
  exact
    AvramDividend.Classical.avram_pj_workerC_original_allphysical_grids_HJB_and_rightpayment_Q_nonpositive
      X q w C hCfinite hw_gen x D hjump u v δ hu hδ huv hvCap T ρ A hPre

