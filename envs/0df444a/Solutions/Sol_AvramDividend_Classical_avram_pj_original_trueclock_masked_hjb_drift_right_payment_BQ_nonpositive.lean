-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_trueclock_masked_hjb_drift_right_payment_BQ_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:49:38.643978+00:00
-- url     : https://prove2.me/submissions/64443b4e-1c1a-47e3-93d6-7fa0c60edebf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_stopped_interior_HJB_B_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_subordinate_stop_fullmark_physical_true_Stieltjes_right_payment_Q_nonpos
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
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
    (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (u v δ : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (huv : u + δ < v) (hvCap : v < C.toReal)
    (n : ℕ) (hn : 0 < n) (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω) :
    let T : ℝ≥0 := (n : ℝ≥0)
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      let R : ℝ≥0 × Ω → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) *
          ((if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
            (if Y p ∈ Icc (u + δ) v then
              X.generator w (Y p) - q * w (Y p) else 0))
      let μT : Measure ℝ≥0 :=
        ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
      let B : (Ω → ℝ≥0) → Ω → ℝ := fun σ ω =>
        ∫ t : ℝ≥0, if t ≤ σ ω then R (t, ω) else 0 ∂μT
      let A : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
        ((Finset.range (k + 1)).image
          (fun i : ℕ => min
            ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
            (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)
      let Q : ℕ → Ω → ℝ := fun k ω =>
        if ρ ω = 0 then 0 else ∑ t ∈ A k ω, Real.exp (-(q * (t : ℝ))) *
          ((rightLimit D t ω - D t ω) -
            (w (riskProcess X x D t ω) -
             w (riskProcess X x D t ω -
               (rightLimit D t ω - D t ω))))
    ∀ k : ℕ, ∀ ω : Ω, B ρ ω + Q k ω ≤ 0 := by
  intro T Y R μT B A Q k ω
  have hB : B ρ ω ≤ 0 :=
    avram_pj_workerC_original_stopped_interior_HJB_B_nonpositive
      X q w C hCfinite hw_gen x D
      u v δ hu hδ huv hvCap T ρ ω
  have hQ : Q k ω ≤ 0 :=
    avram_pj_original_subordinate_stop_fullmark_physical_true_Stieltjes_right_payment_Q_nonpos
      X x C D hD q w hjump n hn τ ρ hτeq hρle k ω
  exact add_nonpos hB hQ
