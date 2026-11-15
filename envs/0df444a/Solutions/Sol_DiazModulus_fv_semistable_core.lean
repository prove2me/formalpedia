-- Prove2me | solution 1 for DiazModulus.fv_semistable_core
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:40:12.368724+00:00
-- url     : https://prove2.me/submissions/37cbea8f-b73b-4f10-ab04-f2b310d7d841

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fv_dot_orthogonal
import Theorems.Thm_DiazModulus_fv_gram_zero_block

open Complex ComplexConjugate

/-! # The semistable case, relative form

Write `n₀ = dim W₀`, `d₀ = dim X₀ > n₀`, `ℓ = dim Y`. Roy's Corollary 1 for the Gram pairing of `X₀`
and `Y` gives `X₁ ⊂ X₀` of dimension `d′ ≥ 1` and `Y₁ ⊂ Y` of dimension `ℓ − ℓ′` with `X₁ · Y₁ = 0`
and `d₀ℓ′ ≤ r(d′ + ℓ′)`, where `r` is the dimension of the ℂ-span of `X₀`; this span lies in `W₀`, so
`r ≤ n₀` and `(d₀ − n₀)ℓ′ ≤ n₀d′`. Let `W` be the ℂ-span of `X₁`, of dimension `w ≥ 1`. Since
`X₁ ⊂ X₀ ∩ W`, relative semistability gives `n₀d′ ≤ d₀w`. Let `V` be the orthogonal of `W` for the
dot product: it has codimension `w`, so `V ≠ ℂⁿ`, and `Y₁ ⊂ Y ∩ V`, so the codimension of `Y ∩ V` in
`Y` is at most `ℓ′`. Chaining, `(d₀ − n₀)·(ℓ − dim(Y ∩ V)) ≤ (d₀ − n₀)ℓ′ ≤ n₀d′ ≤ d₀w`. -/

namespace RC3_SC
open DiazModulus

/-- A vector orthogonal to a set is orthogonal to its ℂ-span. -/
theorem dot_zero_spanC {n : ℕ} {S : Set (Fin n → ℂ)} {y : Fin n → ℂ} (h : ∀ s ∈ S, s ⬝ᵥ y = 0) :
    ∀ w ∈ Submodule.span ℂ S, w ⬝ᵥ y = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem s hs => exact h s hs
  | zero => exact zero_dotProduct _
  | add a b _ _ ha hb => rw [add_dotProduct, ha, hb, add_zero]
  | smul c a _ ha => rw [smul_dotProduct, ha, smul_zero]

end RC3_SC

open DiazModulus RC3_SC in
theorem solution {n : ℕ} (W₀ : Submodule ℂ (Fin n → ℂ))
    (X₀ Y : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X₀] [FiniteDimensional (↥Qbar) ↥Y]
    (hX₀ : ∀ x ∈ X₀, x ∈ W₀)
    (hss : ∀ W : Submodule ℂ (Fin n → ℂ),
      Module.finrank ℂ ↥W₀ * Module.finrank (↥Qbar) ↥(X₀ ⊓ W.restrictScalars (↥Qbar)) ≤
        Module.finrank (↥Qbar) ↥X₀ * Module.finrank ℂ ↥W)
    (hdn : Module.finrank ℂ ↥W₀ < Module.finrank (↥Qbar) ↥X₀)
    (hXY : ∀ x ∈ X₀, ∀ y ∈ Y, x ⬝ᵥ y ∈ LogAlgTilde) :
    ∃ V : Submodule ℂ (Fin n → ℂ), V ≠ ⊤ ∧
      (Module.finrank (↥Qbar) ↥X₀ - Module.finrank ℂ ↥W₀) *
          (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar))) ≤
        Module.finrank (↥Qbar) ↥X₀ * (n - Module.finrank ℂ ↥V) := by
  obtain ⟨X₁, Y₁, hX₁, hY₁, hd', hz, hroy⟩ :=
    DiazModulus.fv_gram_zero_block X₀ Y (by omega) hXY
  -- `r ≤ n₀`
  have hr : Module.finrank ℂ ↥(Submodule.span ℂ (X₀ : Set (Fin n → ℂ))) ≤ Module.finrank ℂ ↥W₀ :=
    Submodule.finrank_mono (Submodule.span_le.mpr fun x hx => hX₀ x hx)
  -- `W` and its orthogonal `V`
  obtain ⟨V, hVmem, hVW⟩ := DiazModulus.fv_dot_orthogonal (Submodule.span ℂ (X₁ : Set (Fin n → ℂ)))
  have hX₁W : X₁ ≤ X₀ ⊓ (Submodule.span ℂ (X₁ : Set (Fin n → ℂ))).restrictScalars (↥Qbar) :=
    le_inf hX₁ fun x hx => Submodule.subset_span hx
  have hw : 0 < Module.finrank ℂ ↥(Submodule.span ℂ (X₁ : Set (Fin n → ℂ))) := by
    refine Submodule.one_le_finrank_iff.mpr fun hW => ?_
    have hbot : X₁ = ⊥ := (Submodule.eq_bot_iff _).mpr fun x hx => by
      have hxW : x ∈ Submodule.span ℂ (X₁ : Set (Fin n → ℂ)) := Submodule.subset_span hx
      rw [hW] at hxW
      exact (Submodule.mem_bot ℂ).mp hxW
    rw [hbot, finrank_bot] at hd'
    exact lt_irrefl 0 hd'
  have h2 := (Nat.mul_le_mul_left (Module.finrank ℂ ↥W₀) (Submodule.finrank_mono hX₁W)).trans
    (hss (Submodule.span ℂ (X₁ : Set (Fin n → ℂ))))
  have hY₁V : Y₁ ≤ Y ⊓ V.restrictScalars (↥Qbar) := by
    refine le_inf hY₁ fun y hy => ?_
    show y ∈ V
    exact (hVmem y).mpr (dot_zero_spanC fun x hx => hz x hx y hy)
  have h3 := Submodule.finrank_mono hY₁V
  have hroy' := hroy.trans (Nat.mul_le_mul_right _ hr)
  refine ⟨V, fun hV => ?_, ?_⟩
  · rw [hV, finrank_top, Module.finrank_fin_fun] at hVW
    omega
  · generalize Module.finrank (↥Qbar) ↥X₀ = d₀ at *
    generalize Module.finrank ℂ ↥W₀ = n₀ at *
    generalize Module.finrank (↥Qbar) ↥Y = l at *
    generalize Module.finrank (↥Qbar) ↥X₁ = d' at *
    generalize Module.finrank (↥Qbar) ↥Y₁ = m at *
    generalize Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar)) = ρ at *
    generalize Module.finrank ℂ ↥(Submodule.span ℂ (X₁ : Set (Fin n → ℂ))) = w at *
    generalize Module.finrank ℂ ↥V = v at *
    have hc : n - v = w := by omega
    rw [hc]
    -- `(d₀ − n₀)(l − ρ) ≤ (d₀ − n₀)(l − m) ≤ n₀ d′ ≤ d₀ w`
    obtain ⟨k, rfl⟩ : ∃ k, d₀ = n₀ + k := ⟨d₀ - n₀, by omega⟩
    obtain ⟨t, ht⟩ : ∃ t, l - m = t := ⟨_, rfl⟩
    rw [ht] at hroy'
    rw [Nat.add_sub_cancel_left]
    have h1 : k * t ≤ n₀ * d' := by nlinarith
    calc k * (l - ρ) ≤ k * t := Nat.mul_le_mul_left _ (by omega)
      _ ≤ n₀ * d' := h1
      _ ≤ _ := h2
