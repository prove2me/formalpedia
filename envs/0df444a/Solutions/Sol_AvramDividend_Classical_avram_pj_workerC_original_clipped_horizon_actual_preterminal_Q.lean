-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_clipped_horizon_actual_preterminal_Q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:50:46.80506+00:00
-- url     : https://prove2.me/submissions/a94c76da-467e-4549-86a3-6d2819cfd7f3

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
    (n : ℕ) (hn : 0 < n)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let A : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      ((Finset.range (k + 1)).image (fun i : ℕ =>
        min ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0))) (ρ ω))).filter
          (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)
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
    have hMem : t = 0 ∨ t < ρ ω := (Finset.mem_filter.mp ht).2
    rcases hMem with hZero | hStrict
    · exact Or.inl hZero
    · exact Or.inr ((ENNReal.coe_lt_coe.mpr hStrict).trans_le (hρruin ω))
  exact
    AvramDividend.Classical.avram_pj_workerC_original_allphysical_grids_HJB_and_rightpayment_Q_nonpositive
      X q w C hCfinite hw_gen x D hjump u v δ hu hδ huv hvCap T ρ A hPre

