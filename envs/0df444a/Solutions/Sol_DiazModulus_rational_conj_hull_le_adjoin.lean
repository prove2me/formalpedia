-- Prove2me | solution 1 for DiazModulus.rational_conj_hull_le_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-23T07:25:08.095552+00:00
-- url     : https://prove2.me/submissions/82eddce7-140f-4066-b1e3-11a8d60d8e9c

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # For rational `z`, the conjugation hull `W_z` lies in `Q̄(u)` and contains `u⁻¹`

Let `u ∉ Q̄` with `ρ = u ū` algebraic, `K = Q̄(u)` and `W_z = Q̄ + Q̄u + Q̄ū + Q̄z + Q̄z̄` with `z ∈ K`.
Since `u ≠ 0`, `ρ` is a non-zero element of `Q̄`, so `u⁻¹ = ρ⁻¹ ū` is a `Q̄`-multiple of a generator
of `W_z`. For the inclusion `W_z ⊆ K` it suffices that the five generators lie in `K`: `1`, `u` and
`z` do, and `ū = ρ u⁻¹ ∈ K`. For `z̄`, the preimage of `K` under complex conjugation is a subfield
of `ℂ`; it contains `Q̄` (conjugation maps algebraic numbers to algebraic numbers) and `u` (because
`ū ∈ K`), so it is an intermediate field containing `u` and hence contains `K = Q̄(u)`
(`IntermediateField.adjoin_le_iff`). Thus conjugation maps `K` into itself and `z̄ ∈ K`.
-/

namespace R20_hullAdj
open DiazModulus

theorem ne_zero_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 :=
  fun h => hu (h ▸ Subfield.zero_mem _)

/-- Conjugation maps `Q̄` to itself. -/
theorem conj_mem_Qbar {a : ℂ} (ha : a ∈ Qbar) : conj a ∈ Qbar :=
  mem_Qbar_iff.2 ((mem_Qbar_iff.1 ha).algHom (starRingEnd ℂ).toRatAlgHom)

/-- `ū = (u ū) u⁻¹ ∈ Q̄(u)`. -/
theorem conj_u_mem {u : ℂ} (hρ : IsAlgebraic ℚ (u * conj u)) (hu0 : u ≠ 0) :
    conj u ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) := by
  have hρK : u * conj u ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) :=
    IntermediateField.algebraMap_mem _ (⟨u * conj u, mem_Qbar_iff.2 hρ⟩ : ↥Qbar)
  have huK : u⁻¹ ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) :=
    inv_mem (IntermediateField.subset_adjoin _ _ (Set.mem_singleton u))
  rw [show conj u = u * conj u * u⁻¹ by field_simp]
  exact mul_mem hρK huK

/-- Conjugation maps `Q̄(u)` to itself. -/
theorem conj_mem_adjoin {u w : ℂ} (hρ : IsAlgebraic ℚ (u * conj u)) (hu0 : u ≠ 0)
    (hw : w ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ)) :
    conj w ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) := by
  let T : IntermediateField (↥Qbar) ℂ :=
    ((IntermediateField.adjoin Qbar ({u} : Set ℂ)).toSubfield.comap
      (starRingEnd ℂ)).toIntermediateField fun x => Subfield.mem_comap.2
        (IntermediateField.algebraMap_mem (IntermediateField.adjoin Qbar ({u} : Set ℂ))
          (⟨conj (x : ℂ), conj_mem_Qbar x.2⟩ : ↥Qbar))
  have hle : IntermediateField.adjoin Qbar ({u} : Set ℂ) ≤ T :=
    IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 (conj_u_mem hρ hu0))
  exact hle hw

end R20_hullAdj

open DiazModulus R20_hullAdj in
open Polynomial in
theorem solution (u z : ℂ) (hu : u ∉ Qbar) (hρ : IsAlgebraic ℚ (u * conj u))
    (hz : z ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ)) :
    u⁻¹ ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ) ∧
      ∀ w ∈ Submodule.span Qbar ({1, u, conj u, z, conj z} : Set ℂ), w ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) := by
  have hu0 := ne_zero_of_not_mem hu
  refine ⟨?_, fun w hw => ?_⟩
  · let ρ : ↥Qbar := ⟨u * conj u, mem_Qbar_iff.2 hρ⟩
    have h : u⁻¹ = ρ⁻¹ • conj u := by
      show u⁻¹ = (u * conj u)⁻¹ * conj u
      rw [mul_inv, mul_assoc, inv_mul_cancel₀ ((_root_.map_ne_zero _).2 hu0), mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · have hsub : ({1, u, conj u, z, conj z} : Set ℂ) ⊆
        (IntermediateField.adjoin Qbar ({u} : Set ℂ)).toSubalgebra.toSubmodule := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact (IntermediateField.adjoin Qbar ({u} : Set ℂ)).one_mem
      · exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
      · exact conj_u_mem hρ hu0
      · exact hz
      · exact conj_mem_adjoin hρ hu0 hz
    exact Submodule.span_le.2 hsub hw
