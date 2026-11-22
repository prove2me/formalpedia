-- Prove2me | solution 3 for AvramDividend.Classical.avram_ja22_original_limit_gaussian_exact_square_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:52:00.962539+00:00
-- url     : https://prove2.me/submissions/84531fdd-0151-4f4c-8616-139e99fbae27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/- Original-space Gaussian limit second moment transported through a
   zero-Levy-measure witness on the SAME probability space and filtration.
   One already Open source-construction premise is exposed rather than
   replacing the original source with an auxiliary independent process.
   The resulting accepted sketch must remain connected to Avram. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja19_same_filtration_zero_nu_from_intrinsic_gaussian_limit
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by
  obtain ⟨Y, hYnu, hYsigma, hYeq⟩ :=
    avram_ja19_same_filtration_zero_nu_from_intrinsic_gaussian_limit
      X hX hFinite R hR
  intro t
  have hR_ae :
      (fun ω => R t ω) =ᵐ[P]
        (fun ω => Y.X t ω - (t : ℝ) * Y.c) :=
    hYeq.mono (fun ω hω => hω t)
  have hSq_ae :
      (fun ω => (R t ω) ^ 2) =ᵐ[P]
        (fun ω => (Y.X t ω - (t : ℝ) * Y.c) ^ 2) :=
    hR_ae.mono (fun ω hω => congrArg (fun y : ℝ => y ^ 2) hω)
  obtain ⟨hYintegrable, hYmoment⟩ :=
    avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
      Y hYnu t
  constructor
  · exact hYintegrable.congr hSq_ae.symm
  · calc
      (∫ ω, (R t ω) ^ 2 ∂P) =
          ∫ ω, (Y.X t ω - (t : ℝ) * Y.c) ^ 2 ∂P :=
        integral_congr_ae hSq_ae
      _ = (t : ℝ) * Y.σ ^ 2 := hYmoment
      _ = (t : ℝ) * X.σ ^ 2 := by rw [hYsigma]

