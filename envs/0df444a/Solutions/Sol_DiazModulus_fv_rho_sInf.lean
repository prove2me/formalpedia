-- Prove2me | solution 1 for DiazModulus.fv_rho_sInf
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:16:26.296206+00:00
-- url     : https://prove2.me/submissions/8d9f82c9-f782-4f97-84a2-f1b0eb188d5c

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fv_rho_inf

open Complex ComplexConjugate

/-! # Codimension of a Q̄-subspace in the intersection of any family of ℂ-subspaces

Write `ρ(W) = dim Y − dim (Y ∩ W)` for the finite-dimensional `Q̄`-subspace `Y`, let `F` be any family of
`ℂ`-subspaces of `ℂⁿ` with `ρ(V) ≤ D` for `V ∈ F`, and `J = ⋂ F`. By induction on `k ≤ n` we find a
`ℂ`-subspace `W ⊇ J` with `ρ(W) ≤ k·D` and either `W = J` or `dim W + k ≤ n`. Start with `W = ℂⁿ`
(`ρ = 0`). In the step, if `W ≠ J` then `W ⊄ J`, so some `V ∈ F` does not contain `W`; replace `W` by
`W ∩ V`, which still contains `J`, has `ρ(W ∩ V) ≤ ρ(W) + ρ(V) ≤ (k + 1)·D` by the intersection bound,
and has dimension at most `dim W − 1`. At `k = n` either `W = J`, or `dim W = 0`, so `W = 0` and `J = 0 = W`.
Either way `ρ(J) ≤ n·D`. -/

namespace RC4_RS
open DiazModulus

/-- `dim Z − dim (Z ∩ W)`, the codimension of `Z ∩ W` in `Z`. -/
noncomputable def rsRho {n : ℕ} (Z : Submodule (↥Qbar) (Fin n → ℂ)) (W : Submodule ℂ (Fin n → ℂ)) :
    ℕ :=
  Module.finrank (↥Qbar) ↥Z - Module.finrank (↥Qbar) ↥(Z ⊓ W.restrictScalars (↥Qbar))

theorem rsRho_top {n : ℕ} (Z : Submodule (↥Qbar) (Fin n → ℂ)) : rsRho Z ⊤ = 0 := by
  unfold rsRho
  rw [Submodule.restrictScalars_top]
  have : Z ⊓ (⊤ : Submodule (↥Qbar) (Fin n → ℂ)) = Z := inf_top_eq Z
  rw [this, Nat.sub_self]

end RC4_RS

open DiazModulus RC4_RS in
theorem solution {n : ℕ} (Y : Submodule (↥Qbar) (Fin n → ℂ)) [FiniteDimensional (↥Qbar) ↥Y]
    (F : Set (Submodule ℂ (Fin n → ℂ))) (D : ℕ)
    (hD : ∀ V ∈ F, Module.finrank (↥Qbar) ↥Y -
        Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar)) ≤ D) :
    Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ (sInf F).restrictScalars (↥Qbar)) ≤
      n * D := by
  change rsRho Y (sInf F) ≤ n * D
  have hD' : ∀ V ∈ F, rsRho Y V ≤ D := hD
  have P : ∀ k, k ≤ n → ∃ W : Submodule ℂ (Fin n → ℂ), sInf F ≤ W ∧ rsRho Y W ≤ k * D ∧
      (W = sInf F ∨ Module.finrank ℂ ↥W + k ≤ n) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨⊤, le_top, by simp [rsRho_top], Or.inr ?_⟩
      simp [finrank_top]
    | succ k ih =>
      intro hk
      obtain ⟨W, hJW, hρ, hor⟩ := ih (by omega)
      by_cases hW : W = sInf F
      · exact ⟨W, hJW, le_trans hρ (Nat.mul_le_mul_right _ (Nat.le_succ k)), Or.inl hW⟩
      · rcases hor with h | h
        · exact absurd h hW
        have hnot : ¬ W ≤ sInf F := fun h' => hW (le_antisymm h' hJW)
        rw [le_sInf_iff] at hnot
        push Not at hnot
        obtain ⟨V, hVF, hWV⟩ := hnot
        refine ⟨W ⊓ V, le_inf hJW (sInf_le hVF), ?_, Or.inr ?_⟩
        · have h1 : rsRho Y (W ⊓ V) ≤ rsRho Y W + rsRho Y V := DiazModulus.fv_rho_inf Y W V
          have h2 := hD' V hVF
          rw [Nat.succ_mul]
          omega
        · have hlt : W ⊓ V < W := inf_lt_left.2 hWV
          have := Submodule.finrank_lt_finrank_of_lt hlt
          omega
  obtain ⟨W, hJW, hρ, hor⟩ := P n le_rfl
  rcases hor with h | h
  · rw [← h]; exact hρ
  · have h0 : Module.finrank ℂ ↥W = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h0
    have hJ : sInf F = W := le_antisymm hJW (h0 ▸ bot_le)
    rw [hJ]; exact hρ
