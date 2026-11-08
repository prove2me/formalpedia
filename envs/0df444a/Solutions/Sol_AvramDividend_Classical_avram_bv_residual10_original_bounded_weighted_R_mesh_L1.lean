-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_bounded_weighted_R_mesh_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:05:18.589498+00:00
-- url     : https://prove2.me/submissions/a42693fc-491a-42a8-b26a-01120dadb587

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_monotone_R_mesh_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Integrability of an actual original-process weighted residual grid follows
from an integrable fixed-time remainder and bounded coefficients. This is the
compact-localisation interface; the original raw jump sum is preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (R : Ω → ℝ≥0 → ℝ)
    (hR : ∀ ω t, R ω t =
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0))
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i, i < n + 1 → u n i ≤ u n (i + 1))
    (hu0 : u n 0 = 0) (huT : u n (n + 1) ≤ T)
    (a : Ω → ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω, ∀ i ∈ Finset.range (n + 1), |a ω i| ≤ K)
    (hInt : Integrable (fun ω => R ω T) P)
    (hMeas : AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        a ω i * (R ω (u n i) - R ω (u n (i + 1)))) P) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        a ω i * (R ω (u n i) - R ω (u n (i + 1)))) P := by
  classical
  have hDom : ∀ᵐ ω ∂P,
      ‖∑ i ∈ Finset.range (n + 1),
        a ω i * (R ω (u n i) - R ω (u n (i + 1)))‖ ≤
      K * R ω T := by
    filter_upwards [avram_bv_residual10_original_raw_R_ae_monotone X hBV]
      with ω hmono
    have hRmono : Monotone (R ω) := by
      intro s t hst
      rw [hR ω s, hR ω t]
      exact hmono hst
    have hz : R ω 0 = 0 := by
      have hJ0 :
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ (0 : ℝ≥0) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) = 0 := by
        have hImpossible (v : ℝ≥0) :
            ¬ (0 < v ∧ v ≤ (0 : ℝ≥0)) := by
          intro hv
          exact not_lt_of_ge hv.2 hv.1
        have hZeroFun :
            (fun v : ℝ≥0 =>
              if 0 < v ∧ v ≤ (0 : ℝ≥0) then
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
              else (0 : ℝ)) = (fun _ => (0 : ℝ)) := by
          funext v
          exact if_neg (hImpossible v)
        rw [hZeroFun]
        simp
      rw [hR ω 0, hJ0]
      simp [X.X_zero]
    have hpath :
        |∑ i ∈ Finset.range (n + 1),
          a ω i * (R ω (u n i) - R ω (u n (i + 1)))| ≤
        K * (R ω (u n (n + 1)) - R ω (u n 0)) := by
      simpa [hR] using
        (avram_bv_residual10_original_monotone_R_mesh_bound
          X ω u n hu hmono (a ω) K (hBound ω))
    have hnet : R ω (u n (n + 1)) ≤ R ω T := hRmono huT
    have hroot :
        |∑ i ∈ Finset.range (n + 1),
          a ω i * (R ω (u n i) - R ω (u n (i + 1)))| ≤
        K * R ω T := by
      calc
        _ ≤ K * (R ω (u n (n + 1)) - R ω (u n 0)) := hpath
        _ = K * R ω (u n (n + 1)) := by rw [hu0, hz, sub_zero]
        _ ≤ K * R ω T := mul_le_mul_of_nonneg_left hnet hK
    simpa only [Real.norm_eq_abs] using hroot
  exact (hInt.const_mul K).mono' hMeas hDom
