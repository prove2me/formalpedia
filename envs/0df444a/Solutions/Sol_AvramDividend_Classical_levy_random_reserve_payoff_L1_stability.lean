-- Prove2me | solution 1 for AvramDividend.Classical.levy_random_reserve_payoff_L1_stability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:28:36.945161+00:00
-- url     : https://prove2.me/submissions/d8f40f71-ec8d-447d-ba28-4a38c36244d5

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z W : Ω → ℝ)
    (hZ : Integrable (fun ω => f (Z ω + (X.X t ω - X.X s ω))) P)
    (hW : Integrable (fun ω => f (W ω + (X.X t ω - X.X s ω))) P)
    (hDom : Integrable (fun ω => L * |Z ω - W ω|) P) :
    |(∫ ω, f (Z ω + (X.X t ω - X.X s ω)) ∂P) -
      (∫ ω, f (W ω + (X.X t ω - X.X s ω)) ∂P)| ≤
      ∫ ω, L * |Z ω - W ω| ∂P := by
  let Δ : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  let F : Ω → ℝ := fun ω => f (Z ω + Δ ω)
  let G : Ω → ℝ := fun ω => f (W ω + Δ ω)
  let H : Ω → ℝ := fun ω => L * |Z ω - W ω|
  have hdiff : Integrable (fun ω => F ω - G ω) P :=
    hZ.sub hW
  have hpath (ω : Ω) : |F ω - G ω| ≤ H ω := by
    have h := hLip (Z ω + Δ ω) (W ω + Δ ω)
    have heq : (Z ω + Δ ω) - (W ω + Δ ω) =
        Z ω - W ω := by ring
    rw [heq] at h
    exact h
  have hu : (fun ω => F ω - G ω) ≤ᵐ[P] H := by
    filter_upwards [] with ω
    exact (abs_le.mp (hpath ω)).2
  have hl : (fun ω => -(H ω)) ≤ᵐ[P]
      (fun ω => F ω - G ω) := by
    filter_upwards [] with ω
    exact (abs_le.mp (hpath ω)).1
  have hiu :
      (∫ ω, F ω - G ω ∂P) ≤ ∫ ω, H ω ∂P :=
    integral_mono_ae hdiff hDom hu
  have hil :
      (∫ ω, -(H ω) ∂P) ≤ ∫ ω, F ω - G ω ∂P :=
    integral_mono_ae hDom.neg hdiff hl
  have hs : (∫ ω, F ω - G ω ∂P) =
      (∫ ω, F ω ∂P) - (∫ ω, G ω ∂P) :=
    integral_sub hZ hW
  rw [hs] at hiu hil
  have hneg : -(∫ ω, H ω ∂P) ≤
      (∫ ω, F ω ∂P) - (∫ ω, G ω ∂P) := by
    simpa only [integral_neg] using hil
  exact abs_le.mpr ⟨hneg, hiu⟩
