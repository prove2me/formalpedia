-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_original_discounted_full_stieltjes_real_atomic_diffuse_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:06:20.682691+00:00
-- url     : https://prove2.me/submissions/e1625966-2676-43f1-9afc-1f62435b0d96

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- Exact original discounted Stieltjes cash is additive over its complete
right-dividend atomic series and actual atomless measure already in ℝ.
The nonnegative finite discounted budget proves both terms are finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ).toReal =
        (∑' t : A, μ {(t : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))).toReal +
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse).toReal := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  rcases avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
    X x D hD ω T
      (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s)))) with
    ⟨A, μdiffuse, hCount, hMeas, hNull, hAt, hSupport, hFull⟩
  refine ⟨A, μdiffuse, hCount, hMeas, hNull, hAt, hSupport, ?_⟩
  have hCash :
      (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
        ENNReal.ofReal (rightLimit D T ω) :=
    avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
      q hq D hD ω T
  have hTotalFin :
      (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) < ⊤ :=
    lt_of_le_of_lt hCash (by simp)
  have hAddFin :
      (∑' t : A, μ {(t : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) +
      (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) < ⊤ := by
    rw [← hFull]
    exact hTotalFin
  have hAtomFin :
      (∑' t : A, μ {(t : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (le_add_of_nonneg_right bot_le) hAddFin
  have hDiffuseFin :
      (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (le_add_of_nonneg_left bot_le) hAddFin
  calc
    (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ).toReal =
      ((∑' t : A, μ {(t : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) +
       (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse)).toReal :=
         congrArg ENNReal.toReal hFull
    _ = (∑' t : A, μ {(t : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))).toReal +
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse).toReal :=
          ENNReal.toReal_add hAtomFin hDiffuseFin
