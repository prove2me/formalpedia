-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_ae_equal_stages_square_envelope_transfer_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:21:32.47778+00:00
-- url     : https://prove2.me/submissions/0f2d9024-d22e-486a-b0fe-4d60e17685e8

import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Almost-sure equal physical stages inherit a common square-integrable
envelope and square-converge to the same original limit. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F Z : ℕ → Ω → ℝ) (C D : Ω → ℝ)
    (hF2 : ∀ k, Integrable (fun ω => (F k ω)^2) P)
    (hFZ : ∀ k, ∀ᵐ ω ∂P, F k ω = Z k ω)
    (hZD : ∀ k, ∀ᵐ ω ∂P, ‖Z k ω‖ ≤ D ω)
    (hD2 : Integrable (fun ω => (D ω)^2) P)
    (hZlim : ∀ᵐ ω ∂P, Tendsto (fun k => Z k ω)
      atTop (𝓝 (C ω))) :
    (∀ k, AEStronglyMeasurable (fun ω => (F k ω)^2) P) ∧
      Integrable (fun ω => (D ω)^2) P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖(F k ω)^2‖ ≤ (D ω)^2) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => (F k ω)^2)
        atTop (𝓝 ((C ω)^2))) := by
  refine ⟨(fun k => (hF2 k).aestronglyMeasurable), hD2, ?_, ?_⟩
  · intro k
    filter_upwards [hFZ k, hZD k] with ω he hb
    rw [he, norm_pow]
    have hn : 0 ≤ D ω := le_trans (norm_nonneg _) hb
    have hm : 0 ≤ (D ω - ‖Z k ω‖) * (D ω + ‖Z k ω‖) :=
      mul_nonneg (sub_nonneg.mpr hb)
        (add_nonneg hn (norm_nonneg _))
    nlinarith
  · have hAll : ∀ᵐ ω ∂P, ∀ k, F k ω = Z k ω :=
      ae_all_iff.mpr hFZ
    filter_upwards [hAll, hZlim] with ω he hl
    have hf : (fun k => F k ω) = (fun k => Z k ω) := by
      funext k
      exact he k
    have hs : (fun k : ℕ => (F k ω)^2) = (fun k => (Z k ω)^2) := by
      funext k
      rw [he k]
    rw [hs]
    exact hl.pow 2
