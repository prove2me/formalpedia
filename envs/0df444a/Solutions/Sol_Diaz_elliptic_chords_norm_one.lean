-- Prove2me | solution 1 for Diaz.elliptic_chords_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:12:04.214153+00:00
-- url     : https://prove2.me/submissions/eb6bdba8-3b91-4515-af09-a7f5b017fe67

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem solution {k : Subfield ℂ} (hkc : ∀ x ∈ k, conj x ∈ k)
    {u v γ : ℂ} (hu : u ≠ 0) (hγ : γ ∈ k) (hv : v = γ * u) (hmod : ‖v‖ = ‖u‖) :
    γ * conj γ = 1
      ∧ ((∀ x ∈ k, conj x = x) → v = u ∨ v = -u)
      ∧ ((∃ x ∈ k, conj x ≠ x) → ∃ δ ∈ k, δ ≠ 0 ∧ γ = δ / conj δ) := by
  have hnu : ‖u‖ ≠ 0 := by simpa using hu
  have habs : ‖γ‖ = 1 := by
    have : ‖γ‖ * ‖u‖ = ‖u‖ := by
      rw [← norm_mul, ← hv, hmod]
    field_simp at this
    exact this
  have hmain : γ * conj γ = 1 := by
    rw [Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq, habs]
    norm_num
  have hγ0 : γ ≠ 0 := by
    intro h; rw [h] at hmain; simp at hmain
  refine ⟨hmain, ?_, ?_⟩
  · intro hreal
    have hc : conj γ = γ := hreal γ hγ
    have hsq : (γ - 1) * (γ + 1) = 0 := by
      have : γ * γ = 1 := by rw [← hmain, hc]
      linear_combination this
    rcases mul_eq_zero.mp hsq with h | h
    · left; rw [hv]; have : γ = 1 := by linear_combination h
      rw [this]; ring
    · right; rw [hv]; have : γ = -1 := by linear_combination h
      rw [this]; ring
  · intro hcm
    by_cases hne : γ = -1
    · obtain ⟨x, hxk, hx⟩ := hcm
      refine ⟨x - conj x, sub_mem hxk (hkc x hxk), ?_, ?_⟩
      · intro h
        apply hx
        have : conj x = x := by linear_combination -h
        exact this
      · have hcd : conj (x - conj x) = -(x - conj x) := by
          rw [map_sub, Complex.conj_conj]; ring
        rw [hcd, hne]
        have hd0 : x - conj x ≠ 0 := by
          intro h; exact hx (by linear_combination -h)
        field_simp
    · refine ⟨1 + γ, add_mem k.one_mem hγ, ?_, ?_⟩
      · intro h; apply hne; linear_combination h
      · have hcg : conj γ = 1 / γ := by
          field_simp
          linear_combination hmain
        have h1γ : (1 : ℂ) + γ ≠ 0 := by
          intro h; exact hne (by linear_combination h)
        have hd : (1 : ℂ) + 1 / γ ≠ 0 := by
          intro h
          apply h1γ
          field_simp at h
          linear_combination h
        rw [map_add, map_one, hcg, eq_div_iff hd]
        field_simp
        ring
