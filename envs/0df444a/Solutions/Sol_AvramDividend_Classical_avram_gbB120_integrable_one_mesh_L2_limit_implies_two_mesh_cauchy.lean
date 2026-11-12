-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB120_integrable_one_mesh_L2_limit_implies_two_mesh_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:15:30.196789+00:00
-- url     : https://prove2.me/submissions/305106a5-fd56-46da-9538-932ebfd1c306

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hfg : ∀ m, Integrable (fun a => (f m a - g a) ^ 2) μ)
    (hff : ∀ m p, Integrable
      (fun a => (f m a - f p a) ^ 2) μ)
    (hlim : Tendsto
      (fun m => ∫ a, (f m a - g a) ^ 2 ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun nm : ℕ × ℕ =>
        ∫ a, (f nm.1 a - f nm.2 a) ^ 2 ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  let V : ℕ → ℝ := fun m => ∫ a, (f m a - g a) ^ 2 ∂μ
  have hBound (m p : ℕ) :
      (∫ a, (f m a - f p a) ^ 2 ∂μ) ≤
        2 * (V m + V p) := by
    have hPt (a : α) :
        (f m a - f p a) ^ 2 ≤
          2 * ((f m a - g a) ^ 2 + (f p a - g a) ^ 2) := by
      nlinarith [sq_nonneg ((f m a - g a) + (f p a - g a))]
    have hInt : Integrable
        (fun a => 2 * ((f m a - g a) ^ 2 +
          (f p a - g a) ^ 2)) μ :=
      ((hfg m).add (hfg p)).const_mul 2
    calc
      _ ≤ ∫ a, 2 * ((f m a - g a) ^ 2 +
            (f p a - g a) ^ 2) ∂μ :=
        integral_mono (hff m p) hInt hPt
      _ = 2 * (V m + V p) := by
        rw [integral_const_mul, integral_add (hfg m) (hfg p)]
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
  have hFirst : Tendsto (fun nm : ℕ × ℕ => V nm.1)
      atTop (𝓝 (0 : ℝ)) := hlim.comp hFst
  have hSecond : Tendsto (fun nm : ℕ × ℕ => V nm.2)
      atTop (𝓝 (0 : ℝ)) := hlim.comp hSnd
  have hUpper : Tendsto (fun nm : ℕ × ℕ =>
      2 * (V nm.1 + V nm.2)) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hFirst.add hSecond).const_mul (2 : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hUpper
    (fun nm => integral_nonneg (fun _ => sq_nonneg _))
    (fun nm => hBound nm.1 nm.2)
