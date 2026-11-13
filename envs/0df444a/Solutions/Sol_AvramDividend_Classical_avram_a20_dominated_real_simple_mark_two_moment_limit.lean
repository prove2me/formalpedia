-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_dominated_real_simple_mark_two_moment_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:00:17.54772+00:00
-- url     : https://prove2.me/submissions/b203199a-987d-4a0f-993b-58e9b87c3f56

import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ℕ → Ω → ℝ) (J B : Ω → ℝ)
    (m e : ℕ → ℝ) (r v : ℝ)
    (hfMeas : ∀ k, AEStronglyMeasurable (f k) P)
    (hBi : Integrable B P)
    (hBsq : Integrable (fun ω => (B ω) ^ 2) P)
    (hBound : ∀ᵐ ω ∂P, ∀ k, ‖f k ω‖ ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop (𝓝 (J ω)))
    (hM : ∀ k, (∫ ω, f k ω ∂P) = m k)
    (hE : ∀ k, (∫ ω, (f k ω) ^ 2 ∂P) = e k)
    (hMr : Tendsto m atTop (𝓝 r))
    (hEv : Tendsto e atTop (𝓝 v)) :
    Integrable J P ∧ Integrable (fun ω => (J ω) ^ 2) P ∧
      (∫ ω, J ω ∂P) = r ∧
      (∫ ω, (J ω) ^ 2 ∂P) = v := by
  have hJmeas : AEStronglyMeasurable J P :=
    aestronglyMeasurable_of_tendsto_ae atTop hfMeas hLimit
  have hDom : ∀ᵐ ω ∂P, ‖J ω‖ ≤ B ω := by
    filter_upwards [hLimit, hBound] with ω hlim hbd
    exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall hbd)
  have hJI : Integrable J P := hBi.mono' hJmeas hDom
  have hJ2 : Integrable (fun ω => (J ω) ^ 2) P := by
    have hBoundSquare : ∀ᵐ ω ∂P, ‖(J ω) ^ 2‖ ≤ (B ω) ^ 2 := by
      filter_upwards [hDom] with ω hb
      have hb0 : (0 : ℝ) ≤ B ω :=
        le_trans (norm_nonneg (J ω)) hb
      rw [norm_pow]
      nlinarith [mul_nonneg (sub_nonneg.mpr hb)
        (add_nonneg hb0 (norm_nonneg (J ω)))]
    exact hBsq.mono' (hJmeas.pow 2) hBoundSquare
  have hLimitInt :
      Tendsto (fun k => ∫ ω, f k ω ∂P)
        atTop (𝓝 (∫ ω, J ω ∂P)) :=
    tendsto_integral_of_dominated_convergence B hfMeas hBi
      (fun k => hBound.mono (fun ω hw => hw k)) hLimit
  have hRawFirst : (∫ ω, J ω ∂P) = r := by
    have hfn : (fun k => ∫ ω, f k ω ∂P) = m := by
      funext k; exact hM k
    rw [hfn] at hLimitInt
    exact tendsto_nhds_unique hLimitInt hMr
  have hF2Meas : ∀ k, AEStronglyMeasurable
      (fun ω => (f k ω) ^ 2) P := by
    intro k
    exact (hfMeas k).pow 2
  have hB2Dom : ∀ k, ∀ᵐ ω ∂P,
      ‖(f k ω) ^ 2‖ ≤ (B ω) ^ 2 := by
    intro k
    filter_upwards [hBound] with ω hw
    have hk := hw k
    have hb0 : (0 : ℝ) ≤ B ω :=
      le_trans (norm_nonneg (f k ω)) hk
    rw [norm_pow]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk)
      (add_nonneg hb0 (norm_nonneg (f k ω)))]
  have hF2Lim : ∀ᵐ ω ∂P,
      Tendsto (fun k => (f k ω) ^ 2)
        atTop (𝓝 ((J ω) ^ 2)) := by
    filter_upwards [hLimit] with ω hw
    exact hw.pow 2
  have hLimitSq :
      Tendsto (fun k => ∫ ω, (f k ω) ^ 2 ∂P)
        atTop (𝓝 (∫ ω, (J ω) ^ 2 ∂P)) :=
    tendsto_integral_of_dominated_convergence
      (fun ω => (B ω) ^ 2) hF2Meas hBsq hB2Dom hF2Lim
  have hRawSecond : (∫ ω, (J ω) ^ 2 ∂P) = v := by
    have hfe : (fun k => ∫ ω, (f k ω) ^ 2 ∂P) = e := by
      funext k; exact hE k
    rw [hfe] at hLimitSq
    exact tendsto_nhds_unique hLimitSq hEv
  exact ⟨hJI, hJ2, hRawFirst, hRawSecond⟩
