-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:21:09.648996+00:00
-- url     : https://prove2.me/submissions/fccdc857-dcfc-4f27-9fac-296a533e7c40

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The canonical stopped W includes the zero-time right payment and the ruin book reserve.
    Both source branches have nonnegative verification value, without a sign claim on U_ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, 0 ≤ Term ω := by
  have hSmoothPair :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :=
    ⟨fun _ => hw_smooth, fun hb => False.elim (hBV hb)⟩
  have hPost :=
    avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
      X w C hw0 hw_cont hw_neg hw_smooth hw_grad x hxc D hD
  have hBook :=
    avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient
      X w C hC hw0 hw_cont hw_neg hSmoothPair hw_grad x hxc D hD
  intro ω
  have hwW : 0 ≤ w (W ω) := by
    rw [hW ω]
    split_ifs with hbranch
    · exact hPost ω (τ ω)
    · exact hBook ω (τ ω)
  rw [hTerm ω]
  exact mul_nonneg (le_of_lt (Real.exp_pos _)) hwW