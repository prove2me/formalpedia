-- Prove2me | solution 1 for DiazModulus.logAlg_adjoin_circle_point_baker_linear_forms
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T17:54:29.897617+00:00
-- url     : https://prove2.me/submissions/788357b6-c8ff-44da-a414-57aa2ba5b65b

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_logAlg_adjoin_circle_point_baker_number_field_basis

open Complex ComplexConjugate

/-! # Baker's theorem on linear forms, for `ℒ_u = ℒ + ℚu + ℚū`

The derivation of Baker's Th. 1.6 from Th. 4.5 (Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, §4.2.5), with `ℒ` replaced by `ℒ_u`; it only uses
that `ℒ_u` is a `ℚ`-vector space. Suppose `b₀ + Σ_j b_j l_j = 0` with `l` `ℚ`-independent in `ℒ_u`. Let
`K = ℚ(b_1, …, b_n)`, a number field, with a `ℚ`-basis `(β_i)`, and write `b_j = Σ_i c_{ji} β_i` with `c_{ji} ∈ ℚ`.
Then `ℓ'_i = Σ_j c_{ji} l_j` lies in `ℒ_u` (a `ℚ`-submodule), and `Σ_i β_i ℓ'_i = Σ_j b_j l_j = −b₀` is algebraic.
Baker over a number-field basis for `ℒ_u` (`logAlg_adjoin_circle_point_baker_number_field_basis`) gives `ℓ' = 0`.
The `ℚ`-independence of the `l_j` gives `c = 0`, hence every `b_j = 0`, and then the relation reads `b₀ = 0`. -/

namespace R19_B2
open DiazModulus

/-- `ℒ_u` is closed under rational linear combinations, written with complex multiplication. -/
theorem sum_ratCast_mul_mem {u : ℂ} {ι : Type*} [Fintype ι] (q : ι → ℚ) (l : ι → ℂ)
    (h : ∀ j, l j ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ))) :
    ∑ j, (q j : ℂ) * l j ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) :=
  Submodule.sum_mem _ fun j _ => by
    rw [← Rat.smul_def]
    exact Submodule.smul_mem _ _ (h j)

end R19_B2

open DiazModulus R19_B2 in
theorem solution
    (u : ℂ) (hρ : IsAlgebraic ℚ (u * conj u))
    (hu : Transcendental (Subfield.closure (LogAlgTilde : Set ℂ)) u)
    (n : ℕ) (l : Fin n → ℂ) (hl : LinearIndependent ℚ l)
    (hlu : ∀ i, l i ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)))
    (b₀ : ℂ) (b : Fin n → ℂ) (hb₀ : IsAlgebraic ℚ b₀) (hb : ∀ i, IsAlgebraic ℚ (b i))
    (hne : b₀ ≠ 0 ∨ ∃ i, b i ≠ 0) :
    b₀ + ∑ i, b i * l i ≠ 0 := by
  intro hrel
  -- `K = ℚ(b_1, …, b_n)` and a basis `β` of `K` over `ℚ`
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range b)
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x ⟨i, hi⟩ => hi ▸ (hb i).isIntegral
  let β := Module.finBasis ℚ K
  have hmem : ∀ j, b j ∈ K := fun j => IntermediateField.subset_adjoin ℚ _ ⟨j, rfl⟩
  -- `b_j = Σ_i c_{ji} β_i`
  let c : Fin n → Fin (Module.finrank ℚ K) → ℚ := fun j i => β.repr ⟨b j, hmem j⟩ i
  have hbc : ∀ j, b j = ∑ i, (c j i : ℂ) * (β i : ℂ) := by
    intro j
    have h1 := congrArg (fun z : K => (z : ℂ)) (β.sum_repr ⟨b j, hmem j⟩)
    simp only [IntermediateField.coe_sum, Rat.smul_def] at h1
    exact h1.symm
  -- `ℓ'_i = Σ_j c_{ji} l_j ∈ ℒ_u`
  let ℓ' : Fin (Module.finrank ℚ K) → ℂ := fun i => ∑ j, (c j i : ℂ) * l j
  have hℓ' : ∀ i, ℓ' i ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) :=
    fun i => sum_ratCast_mul_mem (fun j => c j i) l hlu
  -- `Σ_i β_i ℓ'_i = Σ_j b_j l_j = -b₀`
  have hsum : ∑ i, (β i : ℂ) * ℓ' i = -b₀ := by
    rw [← eq_neg_of_add_eq_zero_right hrel]
    simp only [ℓ', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hbc j, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- Baker over a number-field basis for `ℒ_u`: `ℓ' = 0`
  have h0 := DiazModulus.logAlg_adjoin_circle_point_baker_number_field_basis u hρ hu K β ℓ' hℓ'
    (by rw [hsum]; exact hb₀.neg)
  -- independence of the `l_j`: `c = 0`, so every `b_j = 0`, and then `b₀ = 0`
  have hc : ∀ j i, c j i = 0 := by
    intro j i
    refine Fintype.linearIndependent_iff.1 hl (fun j => c j i) ?_ j
    simpa [Rat.smul_def] using h0 i
  have hb0 : ∀ j, b j = 0 := by
    intro j
    rw [hbc j]
    simp [hc]
  have hb₀0 : b₀ = 0 := by
    simpa [hb0] using hrel
  rcases hne with h | ⟨i, hi⟩
  · exact h hb₀0
  · exact hi (hb0 i)
