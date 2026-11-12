-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_condexp_upper_of_two_centered_noises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:02:40.31136+00:00
-- url     : https://prove2.me/submissions/6b411a21-c292-464d-a2bc-8ffb151711b9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (F MG MJ : Ω → ℝ)
    (hFI : Integrable F P) (hMGI : Integrable MG P)
    (hMJI : Integrable MJ P)
    (hMG0 : P[MG | 𝓕.rightCont 0] =ᵐ[P] 0)
    (hMJ0 : P[MJ | 𝓕.rightCont 0] =ᵐ[P] 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ b + MG ω + MJ ω) :
    P[F | 𝓕.rightCont 0] ≤ᵐ[P] (fun _ : Ω => b) := by
  let m : MeasurableSpace Ω := 𝓕.rightCont 0
  have hBI : Integrable (fun _ : Ω => b) P := integrable_const b
  have hAI : Integrable (fun ω : Ω => b + MG ω) P := hBI.add hMGI
  have hGI : Integrable (fun ω : Ω => b + MG ω + MJ ω) P :=
    hAI.add hMJI
  have hmono := condExp_mono hFI hGI hUpper (m := m)
  have hfirst := condExp_add hBI hMGI m
  have hsecond := condExp_add hAI hMJI m
  have hc : P[(fun _ : Ω => b) | m] = (fun _ : Ω => b) :=
    condExp_const (𝓕.rightCont.le 0) b
  filter_upwards [hmono, hfirst, hsecond, hMG0, hMJ0]
    with ω hm hf hs hg hj
  change P[MG | m] ω = 0 at hg
  change P[MJ | m] ω = 0 at hj
  have hfun1 : ((fun z : Ω => b + MG z) + MJ) =
      (fun z : Ω => b + MG z + MJ z) := by
    funext z
    rfl
  have hfun2 : ((fun _ : Ω => b) + MG) =
      (fun z : Ω => b + MG z) := by
    funext z
    rfl
  have hs' :
      P[(fun z : Ω => b + MG z + MJ z) | m] ω =
        P[(fun z : Ω => b + MG z) | m] ω + P[MJ | m] ω := by
    rw [hfun1] at hs
    simpa only [Pi.add_apply] using hs
  have hf' :
      P[(fun z : Ω => b + MG z) | m] ω =
        P[(fun _ : Ω => b) | m] ω + P[MG | m] ω := by
    rw [hfun2] at hf
    simpa only [Pi.add_apply] using hf
  calc
    P[F | m] ω ≤ P[(fun z : Ω => b + MG z + MJ z) | m] ω := hm
    _ = P[(fun z : Ω => b + MG z) | m] ω + P[MJ | m] ω := hs'
    _ = (P[(fun _ : Ω => b) | m] ω + P[MG | m] ω) +
        P[MJ | m] ω := by rw [hf']
    _ = b := by simpa [hc, hg, hj]
