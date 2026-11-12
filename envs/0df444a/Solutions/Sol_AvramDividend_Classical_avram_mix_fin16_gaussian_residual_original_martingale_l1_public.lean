-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin16_gaussian_residual_original_martingale_l1_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:47:40.014348+00:00
-- url     : https://prove2.me/submissions/a1bc8f33-95ef-492d-ac7b-101297d88ff0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_anoise22_original_gaussian_cutoff_martingale_l1
import Theorems.Thm_AvramDividend_Classical_avram_anoise27_original_gaussian_residual_uniform_l1_dominator
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Intrinsic same-filtration martingale passes to the physical Gaussian residual limit by L1 conditional expectation stability. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P) :
    (∀ t : ℝ≥0, Integrable (R t) P) ∧
    (∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont s) P (R t) ω = R s ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let F : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω
  have hFI (n : ℕ) (T : ℝ≥0) : Integrable (F n T) P :=
    (avram_anoise22_original_gaussian_cutoff_martingale_l1 X hX hFinite n).1 T
  have hFM (n : ℕ) (T : ℝ≥0) : AEStronglyMeasurable (F n T) P :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n T).mono (𝓕.le T) le_rfl).aestronglyMeasurable
  have hSource (T : ℝ≥0) : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => F n T ω) atTop (nhds (R T ω)) := by
    filter_upwards [hRsource] with ω hω
    exact hω T
  have hDom (T : ℝ≥0) : ∃ G : Ω → ℝ,
      Integrable G P ∧ (∀ n : ℕ, ∀ᵐ ω ∂P, ‖F n T ω‖ ≤ G ω) := by
    simpa only [F] using
      (avram_anoise27_original_gaussian_residual_uniform_l1_dominator
        X hFinite T (hFI 0 T))
  have hRM (T : ℝ≥0) : AEStronglyMeasurable (R T) P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => hFM n T) (hSource T)
  have hRI (T : ℝ≥0) : Integrable (R T) P := by
    obtain ⟨G, hG, hBG⟩ := hDom T
    have hAll : ∀ᵐ ω ∂P, ∀ n : ℕ, ‖F n T ω‖ ≤ G ω := ae_all_iff.mpr hBG
    have hBound : ∀ᵐ ω ∂P, ‖R T ω‖ ≤ G ω := by
      filter_upwards [hAll, hSource T] with ω hω hlim
      exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall hω)
    exact Integrable.mono' hG (hRM T) hBound
  refine ⟨hRI, ?_⟩
  intro s t hst
  obtain ⟨Gt, hGt, htBound⟩ := hDom t
  obtain ⟨Gs, hGs, hsBound⟩ := hDom s
  have hSM (n : ℕ) : StronglyMeasurable[𝓕.rightCont s] (F n s) := by
    exact ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n s).mono (𝓕.le_rightCont s) le_rfl).stronglyMeasurable
  have hCE (n : ℕ) : condExp (𝓕.rightCont s) P (F n t) =ᵐ[P]
      condExp (𝓕.rightCont s) P (F n s) := by
    have hh := (avram_anoise22_original_gaussian_cutoff_martingale_l1
      X hX hFinite n).2 s t hst
    have hSelf : condExp (𝓕.rightCont s) P (F n s) = F n s :=
      condExp_of_stronglyMeasurable (𝓕.rightCont.le s) (hSM n) (hFI n s)
    rw [hSelf]
    exact hh
  have hLimitCE : condExp (𝓕.rightCont s) P (R t) =ᵐ[P]
      condExp (𝓕.rightCont s) P (R s) := by
    exact tendsto_condExp_unique
      (fun n => F n t) (fun n => F n s) (R t) (R s)
      (fun n => hFI n t) (fun n => hFI n s)
      (hSource t) (hSource s) Gt hGt Gs hGs htBound hsBound hCE
  exact hLimitCE.trans
    (condExp_of_aestronglyMeasurable' (𝓕.rightCont.le s) (hRadapt s) (hRI s))
