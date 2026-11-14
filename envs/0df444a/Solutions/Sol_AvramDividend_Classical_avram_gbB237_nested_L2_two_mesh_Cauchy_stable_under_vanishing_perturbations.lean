-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB237_nested_L2_two_mesh_Cauchy_stable_under_vanishing_perturbations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T14:47:21.259747+00:00
-- url     : https://prove2.me/submissions/3464fcfe-09b4-4099-b897-cf1f57e4e825

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

/-- Nested two-mesh energy stability under a vanishing L2 perturbation. -/
theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (f g : ℕ → α → β → ℝ)
    (hff : ∀ m p s, Integrable (fun ω => (f m s ω - f p s ω)^2) ν)
    (hfg : ∀ m s, Integrable (fun ω => (f m s ω - g m s ω)^2) ν)
    (hgg : ∀ m p s, Integrable (fun ω => (g m s ω - g p s ω)^2) ν)
    (hffOuter : ∀ m p, Integrable (fun s => ∫ ω, (f m s ω - f p s ω)^2 ∂ν) μ)
    (hfgOuter : ∀ m, Integrable (fun s => ∫ ω, (f m s ω - g m s ω)^2 ∂ν) μ)
    (hggOuter : ∀ m p, Integrable (fun s => ∫ ω, (g m s ω - g p s ω)^2 ∂ν) μ)
    (hClose : Tendsto (fun m => ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ) atTop (𝓝 (0 : ℝ)))
    (hCauchy : Tendsto (fun mp : ℕ × ℕ => ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun mp : ℕ × ℕ => ∫ s, (∫ ω, (f mp.1 s ω - f mp.2 s ω)^2 ∂ν) ∂μ) atTop (𝓝 (0 : ℝ)) := by
  let V : ℕ → ℝ := fun m => ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ
  let W : ℕ × ℕ → ℝ := fun mp => ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ
  have hBound (m p : ℕ) : (∫ s, (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ∂μ) ≤ 3 * (V m + W (m, p) + V p) := by
    have hInner (s : α) : (∫ ω, (f m s ω - f p s ω)^2 ∂ν) ≤ 3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) + (∫ ω, (g m s ω - g p s ω)^2 ∂ν) + (∫ ω, (f p s ω - g p s ω)^2 ∂ν)) := by
      have hPt (ω : β) : (f m s ω - f p s ω)^2 ≤ 3 * ((f m s ω - g m s ω)^2 + (g m s ω - g p s ω)^2 + (f p s ω - g p s ω)^2) := by
        nlinarith [ sq_nonneg ((f m s ω - g m s ω) - (g m s ω - g p s ω)), sq_nonneg ((f m s ω - g m s ω) + (f p s ω - g p s ω)), sq_nonneg ((g m s ω - g p s ω) + (f p s ω - g p s ω))]
      have hInt : Integrable (fun ω => 3 * ((f m s ω - g m s ω)^2 + (g m s ω - g p s ω)^2 + (f p s ω - g p s ω)^2)) ν := (((hfg m s).add (hgg m p s)).add (hfg p s)).const_mul 3
      calc
        _ ≤ ∫ ω, 3 * ((f m s ω - g m s ω)^2 + (g m s ω - g p s ω)^2 + (f p s ω - g p s ω)^2) ∂ν :=
          integral_mono (hff m p s) hInt hPt
        _ = 3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) + (∫ ω, (g m s ω - g p s ω)^2 ∂ν) + (∫ ω, (f p s ω - g p s ω)^2 ∂ν)) := by
          simpa only [Pi.add_apply, integral_const_mul] using
            congrArg (fun z : ℝ => 3 * z)
              ((integral_add ((hfg m s).add (hgg m p s)) (hfg p s)).trans
                (congrArg (fun z : ℝ => z + (∫ w, (f p s w - g p s w)^2 ∂ν))
                  (integral_add (hfg m s) (hgg m p s))))
    have hIntOuter : Integrable (fun s => 3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) + (∫ ω, (g m s ω - g p s ω)^2 ∂ν) + (∫ ω, (f p s ω - g p s ω)^2 ∂ν))) μ := (((hfgOuter m).add (hggOuter m p)).add (hfgOuter p)).const_mul 3
    calc
      _ ≤ ∫ s, 3 * ((∫ ω, (f m s ω - g m s ω)^2 ∂ν) + (∫ ω, (g m s ω - g p s ω)^2 ∂ν) + (∫ ω, (f p s ω - g p s ω)^2 ∂ν)) ∂μ :=
        integral_mono (hffOuter m p) hIntOuter hInner
      _ = 3 * (V m + W (m, p) + V p) := by
        dsimp [V, W]
        simpa only [Pi.add_apply, integral_const_mul] using
          congrArg (fun z : ℝ => 3 * z)
            ((integral_add ((hfgOuter m).add (hggOuter m p)) (hfgOuter p)).trans
              (congrArg (fun z : ℝ => z + (∫ s, (∫ w, (f p s w - g p s w)^2 ∂ν) ∂μ))
                (integral_add (hfgOuter m) (hggOuter m p))))
  have hFst : Tendsto Prod.fst (atTop : Filter (ℕ × ℕ)) (atTop : Filter ℕ) := by
    simpa only [Filter.prod_atTop_atTop_eq] using (Filter.tendsto_fst (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have hSnd : Tendsto Prod.snd (atTop : Filter (ℕ × ℕ)) (atTop : Filter ℕ) := by
    simpa only [Filter.prod_atTop_atTop_eq] using (Filter.tendsto_snd (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have hFirst : Tendsto (fun mp : ℕ × ℕ => V mp.1) atTop (𝓝 (0 : ℝ)) := hClose.comp hFst
  have hSecond : Tendsto (fun mp : ℕ × ℕ => V mp.2) atTop (𝓝 (0 : ℝ)) := hClose.comp hSnd
  have hMiddle : Tendsto W atTop (𝓝 (0 : ℝ)) := hCauchy
  have hUpper : Tendsto (fun mp : ℕ × ℕ => 3 * (V mp.1 + W mp + V mp.2)) atTop (𝓝 (0 : ℝ)) := by
    simpa using ((hFirst.add hMiddle).add hSecond).const_mul (3 : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    (fun mp => integral_nonneg (fun s => integral_nonneg (fun ω => sq_nonneg _)))
    (fun mp => hBound mp.1 mp.2)
