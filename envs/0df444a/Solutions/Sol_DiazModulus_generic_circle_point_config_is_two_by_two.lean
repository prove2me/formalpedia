-- Prove2me | solution 1 for DiazModulus.generic_circle_point_config_is_two_by_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:46:56.109459+00:00
-- url     : https://prove2.me/submissions/1fbf229f-9dd3-4d99-862e-d42e17034146

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_rank_one_config_separation
import Theorems.Thm_DiazModulus_circle_point_config_card_le_four

open Complex ComplexConjugate

/-!
# A generic configuration in `K + Ku + Kū + Σ K w_k` is `2 × 2` inside `K + Ku + Kū`

Assume `u, w₁, …, w_m` algebraically independent over `K`, and `ρ = u ū ∈ K`. Reindexing
`Fin.cons u w` as `Sum.elim w (fun _ => u)` and applying `AlgebraicIndependent.sumElim_iff`
gives that `u` is transcendental over `K` and that `w` is algebraically independent over
`K[u]`, hence over the field `F = K(u)` (`IntermediateField.algebraicIndependent_adjoin_iff`).
Since `u ≠ 0`, `ū = ρ / u ∈ F`, so `H₀ = K + Ku + Kū ⊆ F`. The separation lemma
`rank_one_config_separation` (applied to `V₀ = H₀`, using
`span (S ∪ range w) = span S ⊔ span (range w)`) puts every product `x i y j` in `H₀`. Then
`circle_point_config_card_le_four` gives `p + q ≤ 4`, and with `p, q ≥ 2` we get `p = q = 2`.
-/

namespace R6_circleGen

open DiazModulus

/-- `K + Ku + Kū` lies in `K(u)` when `u ū ∈ K` and `u ≠ 0`. -/
theorem span_le_adjoin (K : Subfield ℂ) (u : ℂ) (hu : u ≠ 0) (hρ : u * conj u ∈ K) :
    ∀ v ∈ Submodule.span K ({1, u, conj u} : Set ℂ),
      v ∈ IntermediateField.adjoin K ({u} : Set ℂ) := by
  intro v hv
  have hle : Submodule.span K ({1, u, conj u} : Set ℂ) ≤
      (IntermediateField.adjoin K ({u} : Set ℂ)).toSubalgebra.toSubmodule := by
    rw [Submodule.span_le]
    have hU : u ∈ IntermediateField.adjoin K ({u} : Set ℂ) :=
      IntermediateField.subset_adjoin K _ (Set.mem_singleton u)
    have hR : u * conj u ∈ IntermediateField.adjoin K ({u} : Set ℂ) :=
      IntermediateField.algebraMap_mem _ (⟨u * conj u, hρ⟩ : K)
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact (IntermediateField.adjoin K ({u} : Set ℂ)).one_mem
    · exact hU
    · have : conj u = (u * conj u) / u := by field_simp
      show conj u ∈ IntermediateField.adjoin K ({u} : Set ℂ)
      rw [this]
      exact IntermediateField.div_mem _ hR hU
  exact hle hv

/-- Splitting `Fin.cons u w` into `u` and `w` over `K(u)`. -/
theorem split (K : Subfield ℂ) (u : ℂ) (m : ℕ) (w : Fin m → ℂ)
    (hgen : AlgebraicIndependent K (Fin.cons u w : Fin (m + 1) → ℂ)) :
    Transcendental K u ∧
      AlgebraicIndependent (IntermediateField.adjoin K ({u} : Set ℂ)).toSubfield w := by
  let f : Fin m ⊕ Unit → Fin (m + 1) := Sum.elim Fin.succ (fun _ => 0)
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) h
    · simp only [f, Sum.elim_inl, Fin.succ_inj] at h; rw [h]
    · exact absurd h (Fin.succ_ne_zero a)
    · exact absurd h.symm (Fin.succ_ne_zero b)
    · rfl
  have hc : (Fin.cons u w : Fin (m + 1) → ℂ) ∘ f = Sum.elim w (fun _ : Unit => u) := by
    funext k
    rcases k with k | k <;> simp [f]
  have h2 := hgen.comp f hf
  rw [hc, AlgebraicIndependent.sumElim_iff] at h2
  obtain ⟨h1, h3⟩ := h2
  refine ⟨by simpa using h1.transcendental (), ?_⟩
  rw [Set.range_const, ← IntermediateField.algebraicIndependent_adjoin_iff] at h3
  exact h3

end R6_circleGen

open DiazModulus R6_circleGen in
theorem solution (K : Subfield ℂ) (u : ℂ)
    (hρ : u * conj u ∈ K) (m : ℕ) (w : Fin m → ℂ)
    (hgen : AlgebraicIndependent K (Fin.cons u w : Fin (m + 1) → ℂ))
    (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (x : Fin p → ℂ) (y : Fin q → ℂ)
    (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span K (({1, u, conj u} : Set ℂ) ∪ Set.range w)) :
    p = 2 ∧ q = 2 ∧ ∀ i j, x i * y j ∈ Submodule.span K ({1, u, conj u} : Set ℂ) := by
  obtain ⟨hT, hw⟩ := split K u m w hgen
  have hu : u ≠ 0 := by
    rintro rfl
    exact hT isAlgebraic_zero
  set F : Subfield ℂ := (IntermediateField.adjoin K ({u} : Set ℂ)).toSubfield
  have hKF : K ≤ F := fun z hz =>
    IntermediateField.algebraMap_mem (IntermediateField.adjoin K ({u} : Set ℂ)) (⟨z, hz⟩ : K)
  have hsep := DiazModulus.rank_one_config_separation K F hKF
    (Submodule.span K ({1, u, conj u} : Set ℂ)) (span_le_adjoin K u hu hρ) m w hw p q hp hq
    x y hx hy (fun i j => by rw [← Submodule.span_union]; exact hxy i j)
  have h4 := DiazModulus.circle_point_config_card_le_four K u hT hρ p q (by omega) (by omega)
    x y hx hy hsep
  exact ⟨by omega, by omega, hsep⟩
