-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB217_nested_L2_one_mesh_implies_two_mesh_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:26:20.337842+00:00
-- url     : https://prove2.me/submissions/24ea2112-d91f-4d1a-b8ea-a71a540d8d58

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section
/-- L2 common limits imply double-mesh energy convergence by two integral monotonicity steps. -/
theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (f : ℕ → α → β → ℝ) (g : α → β → ℝ)
    (hfg : ∀ m t, Integrable
      (fun ω => (f m t ω - g t ω)^2) ν)
    (hff : ∀ m p t, Integrable
      (fun ω => (f m t ω - f p t ω)^2) ν)
    (hfgOuter : ∀ m, Integrable
      (fun t => ∫ ω, (f m t ω - g t ω)^2 ∂ν) μ)
    (hffOuter : ∀ m p, Integrable
      (fun t => ∫ ω, (f m t ω - f p t ω)^2 ∂ν) μ)
    (hlim : Tendsto (fun m =>
      ∫ t, (∫ ω, (f m t ω - g t ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun mp : ℕ × ℕ =>
      ∫ t, (∫ ω, (f mp.1 t ω - f mp.2 t ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  let V : ℕ → ℝ := fun m =>
    ∫ t, (∫ ω, (f m t ω - g t ω)^2 ∂ν) ∂μ
  have hBound (m p : ℕ) :
      (∫ t, (∫ ω, (f m t ω - f p t ω)^2 ∂ν) ∂μ) ≤
      2 * (V m + V p) := by
    have hInner (t : α) :
        (∫ ω, (f m t ω - f p t ω)^2 ∂ν) ≤
        2 * ((∫ ω, (f m t ω - g t ω)^2 ∂ν) +
          (∫ ω, (f p t ω - g t ω)^2 ∂ν)) := by
      have hPt (ω : β) :
          (f m t ω - f p t ω)^2 ≤
          2 * ((f m t ω - g t ω)^2 +
            (f p t ω - g t ω)^2) := by
        nlinarith [sq_nonneg
          ((f m t ω - g t ω) + (f p t ω - g t ω))]
      have hInt : Integrable (fun ω =>
          2 * ((f m t ω - g t ω)^2 +
            (f p t ω - g t ω)^2)) ν :=
        ((hfg m t).add (hfg p t)).const_mul 2
      calc
        _ ≤ ∫ ω, 2 * ((f m t ω - g t ω)^2 +
              (f p t ω - g t ω)^2) ∂ν :=
          integral_mono (hff m p t) hInt hPt
        _ = 2 * ((∫ ω, (f m t ω - g t ω)^2 ∂ν) +
              (∫ ω, (f p t ω - g t ω)^2 ∂ν)) := by
          rw [integral_const_mul, integral_add (hfg m t) (hfg p t)]
    have hIntOuter : Integrable (fun t =>
        2 * ((∫ ω, (f m t ω - g t ω)^2 ∂ν) +
          (∫ ω, (f p t ω - g t ω)^2 ∂ν))) μ :=
      ((hfgOuter m).add (hfgOuter p)).const_mul 2
    calc
      _ ≤ ∫ t, 2 * ((∫ ω, (f m t ω - g t ω)^2 ∂ν) +
            (∫ ω, (f p t ω - g t ω)^2 ∂ν)) ∂μ :=
        integral_mono (hffOuter m p) hIntOuter hInner
      _ = 2 * (V m + V p) := by
        rw [integral_const_mul, integral_add (hfgOuter m) (hfgOuter p)]
  have hFst : Tendsto Prod.fst
      (atTop : Filter (ℕ × ℕ)) (atTop : Filter ℕ) := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_fst (f := (atTop : Filter ℕ))
        (g := (atTop : Filter ℕ)))
  have hSnd : Tendsto Prod.snd
      (atTop : Filter (ℕ × ℕ)) (atTop : Filter ℕ) := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_snd (f := (atTop : Filter ℕ))
        (g := (atTop : Filter ℕ)))
  have hFirst : Tendsto (fun mp : ℕ × ℕ => V mp.1)
      atTop (𝓝 (0 : ℝ)) := hlim.comp hFst
  have hSecond : Tendsto (fun mp : ℕ × ℕ => V mp.2)
      atTop (𝓝 (0 : ℝ)) := hlim.comp hSnd
  have hUpper : Tendsto (fun mp : ℕ × ℕ =>
      2 * (V mp.1 + V mp.2)) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hFirst.add hSecond).const_mul (2 : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hUpper
    (fun mp => integral_nonneg (fun t =>
      integral_nonneg (fun ω => sq_nonneg _)))
    (fun mp => hBound mp.1 mp.2)
