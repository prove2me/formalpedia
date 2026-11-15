-- Prove2me | solution 1 for DiazModulus.dalag_psi_floor_roy_phi
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:10:22.129176+00:00
-- url     : https://prove2.me/submissions/93afeb26-c1bb-4154-b6e1-26d5a85cecb3

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_lemma_phi

open Complex ComplexConjugate

/-! # The integer part of Roy's maximum is DALAG's Ψ

For `0 < n < d` let `F(n, d)` be the closed form of Roy's maximum: `nd/(d − n)` if `n = 1` or `d − n = 1`, and
`(d − n)/(d − n − 1) + (n − 1)n` otherwise. By Roy's Lemma `F(n, d)` is the value of some decomposition of `(n, d)`
and bounds the value of every decomposition. So it suffices to show `Ψ(n, d) ≤ F(n, d) < Ψ(n, d) + 1`, row by row
of the table, with `δ = d − n`:
`n = 1, δ = 1`: `F = 2 = Ψ`; `n = 1, δ ≥ 2`: `F = 1 + 1/δ ∈ (1, 3/2]`, `Ψ = 1`;
`n ≥ 2, δ = 1`: `F = n(n + 1) = Ψ`; `n ≥ 2, δ = 2`: `F = n(n − 1) + 2 = Ψ`;
`n ≥ 2, δ ≥ 3`: `F = n(n − 1) + 1 + 1/(δ − 1)` with `0 < 1/(δ − 1) ≤ 1/2`, `Ψ = n(n − 1) + 1`.
Then every value is `≤ F < Ψ + 1`, and the maximising decomposition has value `F ≥ Ψ`. -/

namespace RC4_R2
open DiazModulus

/-- The closed form of Roy's maximum (same formula as Roy's Lemma). -/
def Fq (n d : ℕ) : ℚ :=
  if n = 1 ∨ d - n = 1 then ((n : ℚ) * d) / ((d : ℚ) - n)
  else ((d : ℚ) - n) / ((d : ℚ) - n - 1) + ((n : ℚ) - 1) * n

/-- DALAG's table (same encoding as the statement). -/
def Psi (a b : ℕ) : ℕ :=
  if a = 0 then 0
  else if a = 1 ∧ 3 ≤ b then 1
  else if 2 ≤ a ∧ a + 3 ≤ b then a * (a - 1) + 1
  else if 2 ≤ a ∧ a + 2 = b then a * (a - 1) + 2
  else if a + 1 = b then a * (a + 1)
  else 0

theorem roy {n d : ℕ} (hn : 0 < n) (hnd : n < d) :
    IsGreatest
      {x : ℚ | ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧
        (D.map Prod.fst).sum = n ∧ (D.map Prod.snd).sum = d ∧
        x = (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum} (Fq n d) :=
  DiazModulus.roy_lemma_phi hn hnd

/-- The rows of the table with `n = 1`. -/
theorem row_one (δ : ℕ) (hδ : 1 ≤ δ) :
    (Psi 1 (1 + δ) : ℚ) ≤ Fq 1 (1 + δ) ∧ Fq 1 (1 + δ) < Psi 1 (1 + δ) + 1 := by
  have hδq : (1 : ℚ) ≤ δ := by exact_mod_cast hδ
  simp only [Fq, Nat.add_sub_cancel_left, Nat.cast_add, add_sub_cancel_left]
  by_cases hδ1 : δ = 1
  · subst hδ1
    have hΨ : Psi 1 (1 + 1) = 2 := by decide
    rw [hΨ]; norm_num
  · have hΨ : Psi 1 (1 + δ) = 1 := by unfold Psi; split_ifs <;> omega
    have h3 : (2 : ℚ) ≤ δ := by exact_mod_cast (show 2 ≤ δ by omega)
    rw [hΨ]
    simp only [true_or, if_true]
    push_cast
    constructor
    · rw [le_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith

/-- The rows of the table with `n ≥ 2`. -/
theorem row_ge_two (n δ : ℕ) (hn : 2 ≤ n) (hδ : 1 ≤ δ) :
    (Psi n (n + δ) : ℚ) ≤ Fq n (n + δ) ∧ Fq n (n + δ) < Psi n (n + δ) + 1 := by
  have hn2 : (2 : ℚ) ≤ n := by exact_mod_cast hn
  simp only [Fq, Nat.add_sub_cancel_left, Nat.cast_add, add_sub_cancel_left]
  by_cases hδ1 : δ = 1
  · subst hδ1
    have hΨ : Psi n (n + 1) = n * (n + 1) := by unfold Psi; split_ifs <;> first | rfl | omega
    rw [hΨ, if_pos (Or.inr rfl)]
    push_cast
    rw [div_one]
    constructor <;> linarith
  · by_cases hδ2 : δ = 2
    · subst hδ2
      have hΨ : Psi n (n + 2) = n * (n - 1) + 2 := by
        unfold Psi; split_ifs <;> first | rfl | omega
      rw [hΨ, if_neg (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
      norm_num
      constructor <;> nlinarith
    · have hΨ : Psi n (n + δ) = n * (n - 1) + 1 := by
        unfold Psi; split_ifs <;> first | rfl | omega
      have h3 : (3 : ℚ) ≤ δ := by exact_mod_cast (show 3 ≤ δ by omega)
      rw [hΨ, if_neg (by omega)]
      push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
      have a1 : 1 ≤ (δ : ℚ) / (δ - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
      have a2 : (δ : ℚ) / (δ - 1) < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
      constructor <;> nlinarith

theorem psi_le_F_lt {n d : ℕ} (hn : 0 < n) (hnd : n < d) :
    (Psi n d : ℚ) ≤ Fq n d ∧ Fq n d < Psi n d + 1 := by
  obtain ⟨δ, rfl⟩ : ∃ δ, d = n + δ := ⟨d - n, by omega⟩
  by_cases h1 : n = 1
  · subst h1; exact row_one δ (by omega)
  · exact row_ge_two n δ (by omega) (by omega)

theorem main {n d : ℕ} (hn : 0 < n) (hnd : n < d) :
    (∀ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) → (D.map Prod.fst).sum = n →
        (D.map Prod.snd).sum = d →
        (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum < (Psi n d : ℚ) + 1) ∧
    ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧ (D.map Prod.fst).sum = n ∧
      (D.map Prod.snd).sum = d ∧
      (Psi n d : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  have hR := roy hn hnd
  have hF := psi_le_F_lt hn hnd
  refine ⟨fun D hD h1 h2 => ?_, ?_⟩
  · have := hR.2 ⟨D, hD, h1, h2, rfl⟩
    linarith [hF.2]
  · obtain ⟨D, hD, h1, h2, h3⟩ := hR.1
    exact ⟨D, hD, h1, h2, by rw [← h3]; exact hF.1⟩

end RC4_R2

open DiazModulus RC4_R2 in
theorem solution {n d : ℕ} (hn : 0 < n) (hnd : n < d) :
    let Ψ : ℕ → ℕ → ℕ := fun a b =>
      if a = 0 then 0
      else if a = 1 ∧ 3 ≤ b then 1
      else if 2 ≤ a ∧ a + 3 ≤ b then a * (a - 1) + 1
      else if 2 ≤ a ∧ a + 2 = b then a * (a - 1) + 2
      else if a + 1 = b then a * (a + 1)
      else 0
    (∀ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) → (D.map Prod.fst).sum = n →
        (D.map Prod.snd).sum = d →
        (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum < (Ψ n d : ℚ) + 1) ∧
    ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ p.1 < p.2) ∧ (D.map Prod.fst).sum = n ∧
      (D.map Prod.snd).sum = d ∧
      (Ψ n d : ℚ) ≤ (D.map fun p : ℕ × ℕ => ((p.1 : ℚ) * p.2) / ((p.2 : ℚ) - p.1)).sum := by
  intro Ψ
  exact main hn hnd
