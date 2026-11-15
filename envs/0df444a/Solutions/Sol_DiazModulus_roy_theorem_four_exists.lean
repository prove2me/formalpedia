-- Prove2me | solution 1 for DiazModulus.roy_theorem_four_exists
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:47:34.070214+00:00
-- url     : https://prove2.me/submissions/37e1ad4f-77ba-4663-b672-71de832d0d82

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_theorem_four
import Theorems.Thm_DiazModulus_multiplicityEstimateElem

open Complex ComplexConjugate

/-! # Roy's Theorem 4 with its minimiser produced

Let `n = dim U`, and for a subspace `S` write `n_S = dim (U ∩ S)`, `d_S = dim S`. Consider the rational
subspaces `S ≠ ℂ^d`. The zero subspace is one of them, since it is rational and `0 < d`. For each such `S`
the numerator `n − n_S` lies in `[0, d]` and the denominator `d − d_S` lies in `[1, d]`, so the ratios
`(n − n_S)/(d − d_S)` take finitely many values and one of them is least; choose `S` attaining it. Clearing the
positive denominators, minimality is exactly the hypothesis `(n − n_S)(d − d_{S'}) ≤ (n − n_{S'})(d − d_S)`
for every rational `S' ≠ ℂ^d` required by Roy's Theorem 4. Theorem 4, applied with the elementary
multiplicity estimate, then gives both inequalities for this `S`. -/

namespace RC2_T4E
open DiazModulus

/-- Among the elements satisfying `C`, some `a₀` minimises the ratio `x a / y a` (finitely many values). -/
theorem exists_min_ratio {α : Type*} (C : α → Prop) (x y : α → ℕ) (N : ℕ)
    (hx : ∀ a, C a → x a ≤ N) (hy : ∀ a, C a → y a ≤ N) (hpos : ∀ a, C a → 0 < y a)
    (hne : ∃ a, C a) : ∃ a₀, C a₀ ∧ ∀ a, C a → x a₀ * y a ≤ x a * y a₀ := by
  classical
  let F : Finset (ℕ × ℕ) := ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter
    (fun p => ∃ a, C a ∧ x a = p.1 ∧ y a = p.2)
  have hmem : ∀ a, C a → (x a, y a) ∈ F := fun a ha =>
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by have := hx a ha; omega),
      Finset.mem_range.mpr (by have := hy a ha; omega)⟩, a, ha, rfl, rfl⟩
  obtain ⟨a, ha⟩ := hne
  obtain ⟨p, hpF, hpmin⟩ := F.exists_min_image (fun p => (p.1 : ℚ) / p.2) ⟨_, hmem a ha⟩
  obtain ⟨a₀, ha₀, hx₀, hy₀⟩ := (Finset.mem_filter.mp hpF).2
  refine ⟨a₀, ha₀, fun b hb => ?_⟩
  have h := hpmin _ (hmem b hb)
  simp only [← hx₀, ← hy₀] at h
  rw [div_le_div_iff₀ (by exact_mod_cast hpos a₀ ha₀) (by exact_mod_cast hpos b hb)] at h
  exact_mod_cast h

end RC2_T4E

open DiazModulus RC2_T4E in
theorem solution {d ℓ : ℕ} (hd : 0 < d) (U : Submodule ℂ (Fin d → ℂ))
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U) (hz : ∀ i j, z i j ∈ LogAlgTilde)
    (hzind : LinearIndependent (↥Qbar) z) :
    ∃ S : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S ∧ S ≠ ⊤ ∧
      (∀ S' : Submodule ℂ (Fin d → ℂ),
        Submodule.span ℂ {v : Fin d → ℂ | v ∈ S' ∧ ∀ i, v i ∈ Qbar} = S' → S' ≠ ⊤ →
        (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) * (d - Module.finrank ℂ ↥S') ≤
          (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S')) * (d - Module.finrank ℂ ↥S)) ∧
      (ℓ - Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓ S.restrictScalars (↥Qbar))) *
          (d - Module.finrank ℂ ↥S) ≤
        (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) *
          ((d - Module.finrank ℂ ↥S) +
            (ℓ - Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓ S.restrictScalars (↥Qbar)))) ∧
      (Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S)) * d ≤
        Module.finrank ℂ ↥U * (d - Module.finrank ℂ ↥S) := by
  have hUd : Module.finrank ℂ ↥U ≤ d := by
    simpa using Submodule.finrank_le U
  obtain ⟨S, ⟨hSrat, hStop⟩, hSmin⟩ := exists_min_ratio
    (fun S : Submodule ℂ (Fin d → ℂ) =>
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, v i ∈ Qbar} = S ∧ S ≠ ⊤)
    (fun S => Module.finrank ℂ ↥U - Module.finrank ℂ ↥(U ⊓ S))
    (fun S => d - Module.finrank ℂ ↥S) d (fun _ _ => by omega) (fun _ _ => by omega)
    (fun T hT => by
      have := Submodule.finrank_lt hT.2
      simp only [Module.finrank_fin_fun] at this
      omega)
    ⟨⊥, le_antisymm (Submodule.span_le.mpr fun v hv => hv.1) bot_le, fun h => by
      have := congrArg (fun T : Submodule ℂ (Fin d → ℂ) => Module.finrank ℂ ↥T) h
      simp at this
      omega⟩
  have hmin := fun S' hS' hS'top => hSmin S' ⟨hS', hS'top⟩
  exact ⟨S, hSrat, hStop, hmin,
    DiazModulus.roy_theorem_four DiazModulus.multiplicityEstimateElem U z hzU hz hzind S hSrat hStop hmin⟩
