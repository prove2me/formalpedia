-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.reorderGap_sign_change
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:47:11.956839+00:00
-- url     : https://prove2.me/submissions/29e24408-d0ab-4446-b534-8741bbaceaaa

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost

namespace GallegoOzerADI.PositiveSetup

theorem aux_rgsc_bdd (V : ℝ → ℝ) (S : ℝ) (hS : ∀ x, V S ≤ V x) (x : ℝ) :
    BddBelow (Set.range (fun y : {y : ℝ // x ≤ y} => V y)) := by
  refine ⟨V S, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hS y

theorem aux_rgsc_inf_le (V : ℝ → ℝ) (S : ℝ) (hS : ∀ x, V S ≤ V x) (x y : ℝ) (hxy : x ≤ y) :
    (⨅ z : {z : ℝ // x ≤ z}, V z) ≤ V y :=
  ciInf_le (aux_rgsc_bdd V S hS x) ⟨y, hxy⟩

theorem aux_rgsc_inf_eq (V : ℝ → ℝ) (S : ℝ) (hS : ∀ x, V S ≤ V x) (x : ℝ) (hxS : x ≤ S) :
    (⨅ z : {z : ℝ // x ≤ z}, V z) = V S := by
  apply le_antisymm
  · exact aux_rgsc_inf_le V S hS x S hxS
  · have : Nonempty {z : ℝ // x ≤ z} := ⟨⟨S, hxS⟩⟩
    exact le_ciInf (fun z => hS z)

end GallegoOzerADI.PositiveSetup

open GallegoOzerADI.PositiveSetup

theorem solution (K : ℝ) (hK : 0 < K) (V : ℝ → ℝ) (hV : ABConvex 0 K V)
    (S : ℝ) (hS : ∀ x, V S ≤ V x) (hiii : ∃ x, x < S ∧ K + V S < V x) :
    (∃ x, reorderGap K V x < 0) ∧ (∃ x, 0 < reorderGap K V x) ∧
      ∀ x₁ x₂, x₁ < x₂ → 0 < reorderGap K V x₁ → 0 ≤ reorderGap K V x₂ := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hxS, hx⟩ := hiii
    refine ⟨x, ?_⟩
    unfold reorderGap
    rw [aux_rgsc_inf_eq V S hS x hxS.le]
    linarith
  · refine ⟨S, ?_⟩
    unfold reorderGap
    rw [aux_rgsc_inf_eq V S hS S le_rfl]
    linarith
  · intro x₁ x₂ h12 hpos
    by_contra hneg0
    have hneg := not_le.mp hneg0
    unfold reorderGap at hneg hpos
    have : Nonempty {z : ℝ // x₂ ≤ z} := ⟨⟨x₂, le_rfl⟩⟩
    have hlt : (⨅ z : {z : ℝ // x₂ ≤ z}, V z) < V x₂ - K := by linarith
    obtain ⟨⟨y, hy⟩, hyv⟩ := exists_lt_of_ciInf_lt hlt
    simp only at hyv
    have hy2 : x₂ < y := by
      rcases hy.lt_or_eq with h | h
      · exact h
      · subst h; linarith
    have h1y : x₁ < y := lt_trans h12 hy2
    set θ : ℝ := (y - x₂) / (y - x₁) with hθ
    have hden : 0 < y - x₁ := by linarith
    have hθ0 : 0 < θ := div_pos (by linarith) hden
    have hθ1 : θ ≤ 1 := by
      rw [div_le_one hden]; linarith
    have hpt : θ * x₁ + (1 - θ) * y = x₂ := by
      rw [hθ]; field_simp; ring
    have hc := hV x₁ y h1y.le θ hθ0.le hθ1
    rw [hpt] at hc
    have h3 : θ * (K + V y) < θ * V x₁ := by nlinarith
    have h4 : K + V y < V x₁ := lt_of_mul_lt_mul_left h3 hθ0.le
    have h5 := aux_rgsc_inf_le V S hS x₁ y h1y.le
    linarith
