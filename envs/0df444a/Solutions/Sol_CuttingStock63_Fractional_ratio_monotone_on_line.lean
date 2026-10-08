-- Prove2me | solution 1 for CuttingStock63.Fractional.ratio_monotone_on_line
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:36:40.659889+00:00
-- url     : https://prove2.me/submissions/f207ccc6-c1bb-4288-a5b5-8923beb6ebd9

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional



namespace CuttingStock63.Fractional
open DermanSeqDecisions.LinProg

theorem rm_core {n : ℕ} (c d x v : Fin n → ℝ) (I : Set ℝ)
    (hI : IsPreconnected I) (hden : ∀ τ ∈ I, ∑ i, d i * (x + τ • v) i ≠ 0) :
    (StrictMonoOn (fun τ : ℝ => fracObj c d (x + τ • v)) I ∨
      StrictAntiOn (fun τ : ℝ => fracObj c d (x + τ • v)) I ∨
      ∀ τ ∈ I, ∀ τ' ∈ I, fracObj c d (x + τ • v) = fracObj c d (x + τ' • v)) ∧
    ∀ τ ∈ I, ∀ τ' ∈ I,
      deriv (fun s : ℝ => fracObj c d (x + s • v)) τ * (∑ i, d i * (x + τ • v) i) ^ 2 =
        deriv (fun s : ℝ => fracObj c d (x + s • v)) τ' * (∑ i, d i * (x + τ' • v) i) ^ 2 := by
  set A := ∑ i, c i * x i with hA
  set B := ∑ i, c i * v i with hB
  set D := ∑ i, d i * x i with hD
  set E := ∑ i, d i * v i with hE
  have hnum : ∀ s : ℝ, ∑ i, c i * (x + s • v) i = A + s * B := by
    intro s; simp [hA, hB, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have hdenf : ∀ s : ℝ, ∑ i, d i * (x + s • v) i = D + s * E := by
    intro s; simp [hD, hE, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have hf : (fun s : ℝ => fracObj c d (x + s • v)) = fun s => (A + s * B) / (D + s * E) := by
    funext s; simp only [fracObj, hnum, hdenf]
  simp only [hdenf] at hden ⊢
  rw [hf]
  have hd : ∀ τ, D + τ * E ≠ 0 → deriv (fun s : ℝ => (A + s * B) / (D + s * E)) τ * (D + τ * E) ^ 2 = B * D - A * E := by
    intro τ h
    have h1 : HasDerivAt (fun s : ℝ => A + s * B) B τ := by
      simpa using ((hasDerivAt_id τ).mul_const B).const_add A
    have h2 : HasDerivAt (fun s : ℝ => D + s * E) E τ := by
      simpa using ((hasDerivAt_id τ).mul_const E).const_add D
    have h3 : HasDerivAt (fun s : ℝ => (A + s * B) / (D + s * E)) ((B * (D + τ * E) - (A + τ * B) * E) / (D + τ * E) ^ 2) τ := h1.div h2 h
    rw [h3.deriv]
    field_simp
    ring
  have hsign : ∀ τ ∈ I, ∀ τ' ∈ I, 0 < (D + τ * E) * (D + τ' * E) := by
    intro τ hτ τ' hτ'
    by_contra hneg
    push_neg at hneg
    have hcont : ContinuousOn (fun s : ℝ => D + s * E) (Set.uIcc τ τ') := by fun_prop
    have h0 : (0:ℝ) ∈ Set.uIcc (D + τ * E) (D + τ' * E) := by
      rw [Set.mem_uIcc]
      rcases lt_or_gt_of_ne (hden τ hτ) with h | h <;> rcases lt_or_gt_of_ne (hden τ' hτ') with h' | h'
      · nlinarith
      · left; exact ⟨h.le, h'.le⟩
      · right; exact ⟨h'.le, h.le⟩
      · nlinarith
    obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc hcont h0
    have hsI : s ∈ I := by
      rcases le_total τ τ' with h | h
      · rw [Set.uIcc_of_le h] at hs; exact hI.Icc_subset hτ hτ' hs
      · rw [Set.uIcc_of_ge h] at hs; exact hI.Icc_subset hτ' hτ hs
    exact hden s hsI hs0
  have hdiff : ∀ τ ∈ I, ∀ τ' ∈ I, (A + τ' * B) / (D + τ' * E) - (A + τ * B) / (D + τ * E)
      = (τ' - τ) * (B * D - A * E) / ((D + τ * E) * (D + τ' * E)) := by
    intro τ hτ τ' hτ'
    have h1 := hden τ hτ; have h2 := hden τ' hτ'
    rw [div_sub_div _ _ h2 h1]
    congr 1 <;> ring
  refine ⟨?_, fun τ hτ τ' hτ' => by rw [hd τ (hden τ hτ), hd τ' (hden τ' hτ')]⟩
  rcases lt_trichotomy (B * D - A * E) 0 with hK | hK | hK
  · right; left
    intro a ha b hb hab
    have := hdiff a ha b hb
    have hp := hsign a ha b hb
    simp only at *
    have : (A + b * B) / (D + b * E) - (A + a * B) / (D + a * E) < 0 := by
      rw [this]; apply div_neg_of_neg_of_pos _ hp
      nlinarith
    linarith
  · right; right
    intro a ha b hb
    have := hdiff a ha b hb
    rw [hK, mul_zero, zero_div] at this
    have e1 := congrFun hf a
    have e2 := congrFun hf b
    rw [e1, e2]
    linarith
  · left
    intro a ha b hb hab
    have := hdiff a ha b hb
    have hp := hsign a ha b hb
    simp only at *
    have : 0 < (A + b * B) / (D + b * E) - (A + a * B) / (D + a * E) := by
      rw [this]; apply div_pos _ hp
      nlinarith
    linarith

end CuttingStock63.Fractional

open CuttingStock63.Fractional
open DermanSeqDecisions.LinProg

theorem solution {n : ℕ} (c d x v : Fin n → ℝ) (I : Set ℝ)
    (hI : IsPreconnected I) (hden : ∀ τ ∈ I, ∑ i, d i * (x + τ • v) i ≠ 0) :
    (StrictMonoOn (fun τ : ℝ => fracObj c d (x + τ • v)) I ∨
      StrictAntiOn (fun τ : ℝ => fracObj c d (x + τ • v)) I ∨
      ∀ τ ∈ I, ∀ τ' ∈ I, fracObj c d (x + τ • v) = fracObj c d (x + τ' • v)) ∧
    ∀ τ ∈ I, ∀ τ' ∈ I,
      deriv (fun s : ℝ => fracObj c d (x + s • v)) τ * (∑ i, d i * (x + τ • v) i) ^ 2 =
        deriv (fun s : ℝ => fracObj c d (x + s • v)) τ' * (∑ i, d i * (x + τ' • v) i) ^ 2 := by
  exact rm_core c d x v I hI hden
