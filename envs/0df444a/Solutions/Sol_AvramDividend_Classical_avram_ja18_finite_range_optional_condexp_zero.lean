-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_finite_range_optional_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:59:37.024679+00:00
-- url     : https://prove2.me/submissions/98af0d96-6daf-4fd9-9caa-08d6beb60dae

import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_ja18_finite_stop_proof_f_91adeaad
import Theorems.Thm_ja18_finite_stop_proof_identity_ccf8a14d
import Theorems.Thm_ja18_finite_stop_proof_identity_4ed333fc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- The conditional-expectation field gives a strongly adapted version.
At a finite-valued stop, the original and modified fields agree off one
finite union of null sets. Optional sampling then applies on the original
right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (J : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T)
    (F : Finset ℝ≥0) (hτF : ∀ ω, τ ω ∈ F)
    (hInt : ∀ t, Integrable (J t) P)
    (hMart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (J t) ω = J s ω)
    (hZero : ∀ᵐ ω ∂P, J 0 ω = 0) :
    Integrable (fun ω => J (τ ω) ω) P ∧
    (∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (fun ω => J (τ ω) ω) ω = 0) := by
  classical
  let f : ℝ≥0 → Ω → ℝ := fun t => P[J t | 𝓕.rightCont t]
  have hf : Martingale f 𝓕.rightCont P := ja18_finite_stop_proof_f_91adeaad (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (J := J) (τ := τ) (T := T) (hτ := hτ) (hτT := hτT) (F := F) (hτF := hτF) (hInt := hInt) (hMart := hMart) (hZero := hZero)
  have hτBound : ∀ ω, (τ ω : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0) := by
    intro ω
    exact_mod_cast hτT ω
  have hCount : (Set.range (fun ω => (τ ω : WithTop ℝ≥0))).Countable := ja18_finite_stop_proof_identity_ccf8a14d (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (J := J) (τ := τ) (T := T) (hτ := hτ) (hτT := hτT) (F := F) (hτF := hτF) (hInt := hInt) (hMart := hMart) (hZero := hZero) (hf := hf) (hτBound := hτBound)
  have hAt (ω : Ω) :
      stoppedValue f (fun ω => (τ ω : WithTop ℝ≥0)) ω =
        f (τ ω) ω := by
    rfl
  have hAll : ∀ᵐ ω ∂P, ∀ t ∈ F, f t ω = J t ω := ja18_finite_stop_proof_identity_4ed333fc (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (J := J) (τ := τ) (T := T) (hτ := hτ) (hτT := hτT) (F := F) (hτF := hτF) (hInt := hInt) (hMart := hMart) (hZero := hZero) (hf := hf) (hτBound := hτBound) (hCount := hCount) (hAt := hAt)
  have hAtAE : (fun ω => J (τ ω) ω) =ᵐ[P]
      (fun ω => stoppedValue f (fun ω => (τ ω : WithTop ℝ≥0)) ω) := by
    filter_upwards [hAll] with ω hω
    rw [hAt]
    exact (hω (τ ω) (hτF ω)).symm
  have hOptional := hf.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτBound hCount
  have hStopped : (fun ω => J (τ ω) ω) =ᵐ[P]
      P[f T | hτ.measurableSpace] := hAtAE.trans hOptional
  have hIntStop : Integrable (fun ω => J (τ ω) ω) P :=
    (integrable_condExp : Integrable (P[f T | hτ.measurableSpace]) P).congr
      hStopped.symm
  have hF0 : 𝓕.rightCont 0 ≤ hτ.measurableSpace :=
    hτ.le_measurableSpace_of_const_le (fun _ => bot_le)
  have hCond :
      P[(fun ω => J (τ ω) ω) | 𝓕.rightCont 0] =ᵐ[P]
        (fun _ : Ω => (0 : ℝ)) := by
    calc
      P[(fun ω => J (τ ω) ω) | 𝓕.rightCont 0] =ᵐ[P]
          P[P[f T | hτ.measurableSpace] | 𝓕.rightCont 0] :=
        condExp_congr_ae hStopped
      _ =ᵐ[P] P[f T | 𝓕.rightCont 0] :=
        condExp_condExp_of_le hF0 (hτ.measurableSpace_le_of_le hτBound)
      _ =ᵐ[P] J 0 := by
        change P[P[J T | 𝓕.rightCont T] | 𝓕.rightCont 0] =ᵐ[P] J 0
        exact (condExp_condExp_of_le
          (𝓕.rightCont.mono (bot_le : (0 : ℝ≥0) ≤ T))
          (𝓕.rightCont.le T)).trans
          (hMart 0 T bot_le)
      _ =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := hZero
  exact ⟨hIntStop, hCond⟩
