-- Prove2me | solution 1 for DiazModulus.dalag_cor_11_15_psi
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:08:06.007478+00:00
-- url     : https://prove2.me/submissions/40e890b7-c653-41a7-8941-59b6d64dccbc

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_theorem_five_dmin
import Theorems.Thm_DiazModulus_dalag_psi_floor_roy_phi

open Complex ComplexConjugate

/-! # DALAG Cor. 11.15 for (Q̄, ℒ̃) in the printed Ψ form

Let `n = dim V` and `s₀ = dim S₀`. Roy's Theorem 5 in its `d_min` form shows that `W = V ∩ ℒ̃^d` is
finite-dimensional over `Q̄` and gives a decomposition `D` of `(n, s₀)` (pairs `0 < nᵢ < dᵢ` with `Σnᵢ = n`,
`Σdᵢ = s₀`) with `ℓ = dim_Q̄ W ≤ Σ nᵢdᵢ/(dᵢ − nᵢ)`. If `n = 0`, every part has `nᵢ > 0`, so `D` is empty, the sum is
`0`, and `ℓ = 0`. If `n > 0`, `D` is non-empty, so `n = Σnᵢ < Σdᵢ = s₀` termwise; then the integer part of Roy's
maximum is DALAG's `Ψ(n, s₀)`: the value of every decomposition is `< Ψ(n, s₀) + 1`. Hence `ℓ < Ψ(n, s₀) + 1`
with both sides integers, i.e. `ℓ ≤ Ψ(n, s₀)`. -/

namespace RC4_R3
open DiazModulus

/-- A non-empty decomposition has `Σ fst < Σ snd`. -/
theorem sums_lt (D : List (ℕ × ℕ)) (hD : ∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) (hne : D ≠ []) :
    (D.map Prod.fst).sum < (D.map Prod.snd).sum := by
  induction D with
  | nil => exact absurd rfl hne
  | cons p D ih =>
    have hp := hD p List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    by_cases hD' : D = []
    · subst hD'; simp only [List.map_nil, List.sum_nil, add_zero]; exact hp.2
    · have := ih (fun q hq => hD q (List.mem_cons_of_mem _ hq)) hD'; omega

/-- The counting step, for any table `Ψ` bounding the decomposition values from above. -/
theorem key (Ψ : ℕ → ℕ → ℕ) {n s ℓ : ℕ} (D : List (ℕ × ℕ)) (hD : ∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2)
    (h1 : (D.map Prod.fst).sum = n) (h2 : (D.map Prod.snd).sum = s)
    (hle : (ℓ : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum)
    (hR2 : 0 < n → n < s →
      (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum < (Ψ n s : ℚ) + 1) :
    (0 < n → n < s) ∧ ℓ ≤ Ψ n s := by
  have hlt : 0 < n → n < s := by
    intro hpos
    have hne : D ≠ [] := by
      rintro rfl
      simp only [List.map_nil, List.sum_nil] at h1
      omega
    rw [← h1, ← h2]
    exact sums_lt D hD hne
  refine ⟨hlt, ?_⟩
  by_cases hn : n = 0
  · have hD0 : D = [] := by
      cases D with
      | nil => rfl
      | cons p D' =>
        exfalso
        have := (hD p List.mem_cons_self).1
        simp only [List.map_cons, List.sum_cons] at h1
        omega
    subst hD0
    simp only [List.map_nil, List.sum_nil] at hle
    have : ℓ = 0 := by exact_mod_cast le_antisymm hle (Nat.cast_nonneg ℓ)
    rw [this]
    exact Nat.zero_le _
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have h' : (ℓ : ℚ) < (Ψ n s : ℚ) + 1 := lt_of_le_of_lt hle (hR2 hpos (hlt hpos))
    have h'' : ℓ < Ψ n s + 1 := by exact_mod_cast h'
    omega

end RC4_R3

open DiazModulus RC4_R3 in
theorem solution {d : ℕ} (V S₀ : Submodule ℂ (Fin d → ℂ))
    (hVQ : ∀ v ∈ V, (∀ i, v i ∈ Qbar) → v = 0)
    (hS₀ : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S₀ ∧ ∀ i, v i ∈ Qbar} = S₀) (hVS₀ : V ≤ S₀)
    (hmin : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → V ≤ T →
        Module.finrank ℂ ↥S₀ ≤ Module.finrank ℂ ↥T) :
    let Ψ : ℕ → ℕ → ℕ := fun a b =>
      if a = 0 then 0
      else if a = 1 ∧ 3 ≤ b then 1
      else if 2 ≤ a ∧ a + 3 ≤ b then a * (a - 1) + 1
      else if 2 ≤ a ∧ a + 2 = b then a * (a - 1) + 2
      else if a + 1 = b then a * (a + 1)
      else 0
    (0 < Module.finrank ℂ ↥V → Module.finrank ℂ ↥V < Module.finrank ℂ ↥S₀) ∧
    FiniteDimensional (↥Qbar)
        ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) ∧
    Module.finrank (↥Qbar)
        ↥(V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin d => LogAlgTilde)) ≤
      Ψ (Module.finrank ℂ ↥V) (Module.finrank ℂ ↥S₀) := by
  intro Ψ
  obtain ⟨hfin, D, hD, h1, h2, hle⟩ := DiazModulus.roy_theorem_five_dmin V S₀ hVQ hS₀ hVS₀ hmin
  have hk := key Ψ D hD h1 h2 hle
    (fun hn hns => (DiazModulus.dalag_psi_floor_roy_phi hn hns).1 D hD h1 h2)
  exact ⟨hk.1, hfin, hk.2⟩
