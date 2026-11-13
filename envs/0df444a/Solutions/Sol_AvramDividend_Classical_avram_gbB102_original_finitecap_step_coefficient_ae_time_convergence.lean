-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB102_original_finitecap_step_coefficient_ae_time_convergence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:43:03.729987+00:00
-- url     : https://prove2.me/submissions/885d854c-e671-4ca3-a427-8fec25a49366
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB162_nnreal_step_clipped_pointwise_convergence_at_good_time
import Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_finitecap_good_times_for_mesh_convergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
    (j : ℕ) :
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let a : ℝ := δ / 2
    let Y : ℝ≥0 → Ω → ℝ := fun s ω =>
      x + X.X s ω - rightLimit D s ω
    let H : ℝ → Ω → ℝ := fun t ω =>
      if (Real.toNNReal t) < ρ ω then
        Real.exp (-(q * t)) *
          (if Y (Real.toNNReal t) ω ∈ Icc a b then
            deriv w (Y (Real.toNNReal t) ω) else 1)
      else 0
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (m + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
          (if Y (s i) ω ∈ Icc a b then deriv w (Y (s i) ω)
            else 1) else 0)
        else 0)
    ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      Tendsto (fun m : ℕ => K m t ω) atTop (𝓝 (H t ω)) := by
  intro b a Y H K
  have hGood := avram_gbB163_original_finitecap_good_times_for_mesh_convergence
    X hX hBV hν q hq w C hC hFiniteCap hw_smooth
    x D hD n hn ρ hρstop δ hδ hFloor j
  filter_upwards [hGood] with ω hω
  filter_upwards [hω, ae_restrict_mem measurableSet_Ioo] with t ht htI
  rcases ht with ⟨hY, hA, hB, hR, hCont⟩
  let YR : ℝ → ℝ := fun s => Y (Real.toNNReal s) ω
  have hCore := avram_gbB162_nnreal_step_clipped_pointwise_convergence_at_good_time
    n hn t htI q w a b YR hY hCont hA hB (ρ ω : ℝ) hR
  have hnn (s : ℝ≥0) : Real.toNNReal (s : ℝ) = s := Real.toNNReal_coe
  have h1 : (Real.toNNReal t : ℝ) = t := Real.coe_toNNReal t (le_of_lt htI.1)
  have hStop : ((Real.toNNReal t) < ρ ω) ↔ t < (ρ ω : ℝ) := by
    rw [← NNReal.coe_lt_coe, h1]
  have hGrid (m : ℕ) :
      (let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
       (Finset.range (m + 1)).sum (fun i =>
         let s : ℝ≥0 := (i : ℝ≥0) * Δ
         if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ) then
           if (s : ℝ) < (ρ ω : ℝ) then
             Real.exp (-(q * (s : ℝ))) *
               (if YR (s : ℝ) ∈ Icc a b then
                 deriv w (YR (s : ℝ)) else 1)
           else 0 else 0)) = K m t ω := by
    simp only [K, YR, hnn, NNReal.coe_lt_coe]
  have hTarget : (if t < (ρ ω : ℝ) then Real.exp (-(q * t)) *
       (if YR t ∈ Icc a b then deriv w (YR t) else 1)
      else 0) = H t ω := by
    simp only [H, YR, hStop, h1]
  simpa only [hGrid, hTarget] using hCore
