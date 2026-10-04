-- Prove2me | solution 1 for Disjunctive.LiftProject.mip_cut_lifting
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:28:37.961+00:00
-- url     : https://prove2.me/submissions/0f28d4ac-a34c-4549-a714-da7ff8fdb589

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic

open Disjunctive.LiftProject

theorem solution : ¬ (∀ {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (j : Fin n) (Nprime : Finset (Fin n))
    (u v : Fin m → ℝ) (u0 v0 : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0) (α : Fin n → ℝ) (β : ℝ)
    (hAlpha : ∀ i, α i = max (Alpha1_64 Atil u u0 j i) (Alpha2_64 Atil v v0 j i))
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbeta1 : β = ∑ ρ, u ρ * btil ρ) (hbeta2 : β = (∑ ρ, v ρ * btil ρ) + v0)
    (γ mbar : Fin n → ℝ)
    (hmbar : ∀ k ∈ Nprime, mbar k = (Alpha2_64 Atil v v0 j k - Alpha1_64 Atil u u0 j k) / (u0 + v0))
    (hgamma1 : ∀ k ∈ Nprime, γ k = min (Alpha1_64 Atil u u0 j k + u0 * (⌈mbar k⌉ : ℝ))
      (Alpha2_64 Atil v v0 j k - v0 * (⌊mbar k⌋ : ℝ)))
    (hgamma2 : ∀ k ∉ Nprime, γ k = max (Alpha1_64 Atil u u0 j k) (Alpha2_64 Atil v v0 j k)),
    ∀ x ∈ MIPDisjunctiveSet Atil btil Nprime, β ≤ dotProduct γ x) := by
  intro h
  have hA1 : Alpha1_64 (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 0) 1 0 0 = -1 := by
    simp [Alpha1_64]
  have hA2 : Alpha2_64 (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1) 1 0 0 = 1 := by
    simp [Alpha2_64]
  have key := h (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => -1) 0 ∅ (fun _ => 0) (fun _ => 1) 1 1
    one_pos one_pos (fun _ => 1) 0
    (fun i => by fin_cases i; simp [hA1, hA2])
    (fun _ => le_rfl) (fun _ => zero_le_one)
    (by simp) (by simp)
    (fun _ => 1) (fun _ => 0)
    (fun k hk => by simp at hk) (fun k hk => by simp at hk)
    (fun k _ => by fin_cases k; simp [hA1, hA2])
    (fun _ => -1) ⟨fun i => by simp, by simp⟩
  simp [dotProduct] at key
  linarith

#print axioms solution
