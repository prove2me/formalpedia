-- Prove2me | solution 1 for DermanSeqDecisions.LinProg.lemma_linear_fractional
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:44:30.586983+00:00
-- url     : https://prove2.me/submissions/25f17dd2-dfa2-4f46-9386-4224196ab2c8

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional

set_option autoImplicit false

theorem lf4ee9ab11_sum_div {ι : Type*} [Fintype ι] (f x : ι → ℝ) (s : ℝ) :
    ∑ i, f i * (x i / s) = (∑ i, f i * x i) / s := by
  rw [Finset.sum_div]; simp [mul_div_assoc]

open DermanSeqDecisions.LinProg in
theorem lf4ee9ab11_pos {ι κ : Type*} [Fintype ι]
    (A : κ → ι → ℝ) (b : κ → ℝ) (d : ι → ℝ)
    (hi : ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → (∀ j, ∑ i, A j i * x i = 0) → ∀ i, x i = 0)
    (z : ι → ℝ) (zlast : ℝ) (h : IsFeasible12 A b d z zlast) : 0 < zlast := by
  obtain ⟨hz, hl, hA, hd⟩ := h
  rcases hl.lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 := hi z hz (fun j => by have := hA j; rw [← h] at this; simpa using this)
    simp [h0] at hd

open DermanSeqDecisions.LinProg in
theorem lf4ee9ab11_fwd {ι κ : Type*} [Fintype ι]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c d : ι → ℝ)
    (hii : ∀ x : ι → ℝ, IsFeasible11 A b x → 0 < ∑ i, d i * x i)
    (x : ι → ℝ) (hx : IsFeasible11 A b x) :
      IsFeasible12 A b d (fun i => x i / ∑ i', d i' * x i') (1 / ∑ i', d i' * x i') ∧
      linObj c (fun i => x i / ∑ i', d i' * x i') = fracObj c d x := by
  have hS := hii x hx
  obtain ⟨hx0, hxA⟩ := hx
  refine ⟨⟨fun i => div_nonneg (hx0 i) hS.le, by positivity, fun j => ?_, ?_⟩, ?_⟩
  · rw [lf4ee9ab11_sum_div, hxA j]; field_simp; ring
  · rw [lf4ee9ab11_sum_div]; field_simp
  · unfold linObj fracObj; rw [lf4ee9ab11_sum_div]

open DermanSeqDecisions.LinProg in
theorem solution {ι κ : Type*} [Fintype ι]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c d : ι → ℝ)
    (hi : ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → (∀ j, ∑ i, A j i * x i = 0) → ∀ i, x i = 0)
    (hii : ∀ x : ι → ℝ, IsFeasible11 A b x → 0 < ∑ i, d i * x i) :
    (∀ (z : ι → ℝ) (zlast : ℝ), IsFeasible12 A b d z zlast → 0 < zlast) ∧
    (∀ x : ι → ℝ, IsFeasible11 A b x →
      IsFeasible12 A b d (fun i => x i / ∑ i', d i' * x i') (1 / ∑ i', d i' * x i') ∧
      linObj c (fun i => x i / ∑ i', d i' * x i') = fracObj c d x) ∧
    (∀ (z : ι → ℝ) (zlast : ℝ), IsFeasible12 A b d z zlast →
      IsFeasible11 A b (fun i => z i / zlast) ∧ fracObj c d (fun i => z i / zlast) = linObj c z ∧
      (fun i => z i / zlast / ∑ i', d i' * (z i' / zlast)) = z ∧
      1 / ∑ i', d i' * (z i' / zlast) = zlast) ∧
    (∀ x : ι → ℝ, IsFeasible11 A b x →
      (fun i => (x i / ∑ i', d i' * x i') / (1 / ∑ i', d i' * x i')) = x) ∧
    (∀ (z : ι → ℝ) (zlast : ℝ), IsFeasible12 A b d z zlast →
      (∀ (z' : ι → ℝ) (zlast' : ℝ), IsFeasible12 A b d z' zlast' → linObj c z ≤ linObj c z') →
      IsFeasible11 A b (fun i => z i / zlast) ∧
      ∀ x' : ι → ℝ, IsFeasible11 A b x' → fracObj c d (fun i => z i / zlast) ≤ fracObj c d x') := by
  have back : ∀ (z : ι → ℝ) (zlast : ℝ), IsFeasible12 A b d z zlast →
      IsFeasible11 A b (fun i => z i / zlast) ∧ fracObj c d (fun i => z i / zlast) = linObj c z ∧
      (fun i => z i / zlast / ∑ i', d i' * (z i' / zlast)) = z ∧
      1 / ∑ i', d i' * (z i' / zlast) = zlast := by
    intro z zlast h
    have hp := lf4ee9ab11_pos A b d hi z zlast h
    obtain ⟨hz, hl, hA, hd⟩ := h
    have hD : ∑ i', d i' * (z i' / zlast) = 1 / zlast := by rw [lf4ee9ab11_sum_div, hd]
    refine ⟨⟨fun i => div_nonneg (hz i) hl, fun j => ?_⟩, ?_, ?_, ?_⟩
    · rw [lf4ee9ab11_sum_div]; have := hA j; field_simp; linarith
    · unfold fracObj linObj; rw [lf4ee9ab11_sum_div, hD]; field_simp
    · funext i; rw [hD]; field_simp
    · rw [hD]; field_simp
  refine ⟨fun z zl h => lf4ee9ab11_pos A b d hi z zl h,
    fun x hx => lf4ee9ab11_fwd A b c d hii x hx, back, ?_, ?_⟩
  · intro x hx
    have hS := hii x hx
    funext i; field_simp
  · intro z zlast h hmin
    obtain ⟨h1, h2, -, -⟩ := back z zlast h
    refine ⟨h1, fun x' hx' => ?_⟩
    obtain ⟨f1, f2⟩ := lf4ee9ab11_fwd A b c d hii x' hx'
    rw [h2, ← f2]
    exact hmin _ _ f1
