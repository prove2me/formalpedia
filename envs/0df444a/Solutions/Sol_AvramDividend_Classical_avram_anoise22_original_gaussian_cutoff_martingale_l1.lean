-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise22_original_gaussian_cutoff_martingale_l1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:23:59.174485+00:00
-- url     : https://prove2.me/submissions/c439490a-5520-4db4-9b9a-965dee79ab93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise29_original_zero_cutoff_gaussian_core_martingale
import Theorems.Thm_AvramDividend_Classical_avram_anoise29_original_bounded_compensated_band_martingale
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every physical residual cutoff equals the original zero-cutoff core minus the original bounded compensated jump band. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n : ℕ,
      (∀ t : ℝ≥0, Integrable
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P) ∧
      (∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P
          (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ω =
        avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let R (n : ℕ) (t : ℝ≥0) (ω : Ω) :=
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω
  let S (n : ℕ) (t : ℝ≥0) (ω : Ω) :=
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
  have hCore := avram_anoise29_original_zero_cutoff_gaussian_core_martingale X hX hFinite
  have hBand := avram_anoise29_original_bounded_compensated_band_martingale X hFinite
  have hPath (n : ℕ) (t : ℝ≥0) : R n t = R 0 t - S n t := by
    funext ω
    have h := avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff X n 0 t ω
    have hZero : S 0 t ω = 0 := by
      simp [S, avram_p4_h_gaussian_intrinsic_small_band_compensated]
    dsimp [R, S] at *
    rw [hZero] at h
    simp only [zero_sub] at h
    linarith
  intro n
  have hI (t : ℝ≥0) : Integrable (R n t) P := by
    rw [hPath n t]
    exact (hCore.1 t).sub ((hBand n).1 t)
  refine ⟨hI, ?_⟩
  intro s t hst
  change condExp (𝓕.rightCont s) P (R n t) =ᵐ[P] R n s
  calc
    condExp (𝓕.rightCont s) P (R n t) =ᵐ[P]
        condExp (𝓕.rightCont s) P (R 0 t - S n t) := by rw [hPath n t]
    _ =ᵐ[P] condExp (𝓕.rightCont s) P (R 0 t) -
        condExp (𝓕.rightCont s) P (S n t) :=
      condExp_sub (hCore.1 t) ((hBand n).1 t) (𝓕.rightCont s)
    _ =ᵐ[P] R 0 s - S n s := by
      filter_upwards [hCore.2 s t hst, (hBand n).2 s t hst] with ω hc hb
      simp only [Pi.sub_apply]
      rw [hc, hb]
    _ =ᵐ[P] R n s := Filter.Eventually.of_forall
      (fun ω => (congrFun (hPath n s) ω).symm)
