-- Prove2me | solution 1 for DiazModulus.fv_max_slope
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:40:09.367324+00:00
-- url     : https://prove2.me/submissions/480cc2b3-d3fc-40b3-84f7-b1a1af31e424

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A ℂ-subspace of maximal slope

For a non-zero ℂ-subspace `W` of `ℂⁿ` the slope of `X` in `W` is `dim_Q̄ (X ∩ W) / dim_ℂ W`. The
numerator lies in `{0, …, dim X}` and the denominator in `{1, …, n}`, so the slope takes finitely many
values; `W = ℂⁿ` is admissible because `n > 0`. Take `W₀` realising the largest value. For `W ≠ 0`
the inequality `σ(W) ≤ σ(W₀)`, multiplied by the positive denominators, is the claim; for `W = 0`
the left side is `0`. -/

namespace RC3_MS
open DiazModulus

/-- A maximiser of the ratio `x a / y a` over a condition with finitely many values. -/
theorem exists_max_ratio {α : Type*} (C : α → Prop) (x y : α → ℕ) (N : ℕ)
    (hx : ∀ a, C a → x a ≤ N) (hy : ∀ a, C a → y a ≤ N) (hpos : ∀ a, C a → 0 < y a)
    (hne : ∃ a, C a) : ∃ a₀, C a₀ ∧ ∀ a, C a → x a * y a₀ ≤ x a₀ * y a := by
  classical
  let F : Finset (ℕ × ℕ) := ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
    (fun p => ∃ a, C a ∧ x a = p.1 ∧ y a = p.2)
  have hmem : ∀ a, C a → (x a, y a) ∈ F := fun a ha =>
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by have := hx a ha; omega),
      Finset.mem_range.mpr (by have := hy a ha; omega)⟩, a, ha, rfl, rfl⟩
  obtain ⟨a, ha⟩ := hne
  obtain ⟨p, hpF, hpmax⟩ := F.exists_max_image (fun p => (p.1 : ℚ) / p.2) ⟨_, hmem a ha⟩
  obtain ⟨a₀, ha₀, hx₀, hy₀⟩ := (Finset.mem_filter.mp hpF).2
  refine ⟨a₀, ha₀, fun b hb => ?_⟩
  have h := hpmax _ (hmem b hb)
  simp only [← hx₀, ← hy₀] at h
  rw [div_le_div_iff₀ (by exact_mod_cast hpos b hb) (by exact_mod_cast hpos a₀ ha₀)] at h
  exact_mod_cast h

end RC3_MS

open DiazModulus RC3_MS in
theorem solution {n : ℕ} (hn : 0 < n) (X : Submodule (↥Qbar) (Fin n → ℂ))
    [FiniteDimensional (↥Qbar) ↥X] :
    ∃ W₀ : Submodule ℂ (Fin n → ℂ), W₀ ≠ ⊥ ∧
      ∀ W : Submodule ℂ (Fin n → ℂ),
        Module.finrank (↥Qbar) ↥(X ⊓ W.restrictScalars (↥Qbar)) * Module.finrank ℂ ↥W₀ ≤
          Module.finrank (↥Qbar) ↥(X ⊓ W₀.restrictScalars (↥Qbar)) * Module.finrank ℂ ↥W := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨W₀, hW₀, hmax⟩ := exists_max_ratio (fun W : Submodule ℂ (Fin n → ℂ) => W ≠ ⊥)
    (fun W => Module.finrank (↥Qbar) ↥(X ⊓ W.restrictScalars (↥Qbar)))
    (fun W => Module.finrank ℂ ↥W) (Module.finrank (↥Qbar) ↥X + n)
    (fun W _ => by have := Submodule.finrank_mono (inf_le_left : X ⊓ W.restrictScalars (↥Qbar) ≤ X); omega)
    (fun W _ => by
      have := Submodule.finrank_le W
      rw [Module.finrank_fin_fun] at this; omega)
    (fun W hW => Submodule.one_le_finrank_iff.mpr hW)
    ⟨⊤, top_ne_bot⟩
  refine ⟨W₀, hW₀, fun W => ?_⟩
  by_cases hW : W = ⊥
  · subst hW
    rw [Submodule.restrictScalars_bot, inf_bot_eq, finrank_bot, zero_mul]; exact Nat.zero_le _
  · exact hmax W hW
