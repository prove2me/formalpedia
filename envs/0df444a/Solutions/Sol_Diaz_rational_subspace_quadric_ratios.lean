-- Prove2me | solution 1 for Diaz.rational_subspace_quadric_ratios
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:17:27.857564+00:00
-- url     : https://prove2.me/submissions/a8a85140-d781-4784-a04b-67ac05954d55

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_rational_singular_subspace_classification

open ComplexConjugate
open Diaz

open Diaz in
theorem solution
    {K : Subfield ℂ} {W : Submodule ℂ (Fin 4 → ℂ)}
    (hK : W ≤ Submodule.span ℂ {z : Fin 4 → ℂ | z ∈ W ∧ ∀ i, z i ∈ K})
    (hQ : ∀ z ∈ W, z 0 * z 1 - z 2 * z 3 = 0)
    {x : Fin 4 → ℂ} (hx : x ∈ W) (hx0 : ∀ i, x i ≠ 0) :
    (x 0 / x 3 ∈ K ∧ x 2 / x 1 ∈ K) ∨ (x 0 / x 2 ∈ K ∧ x 3 / x 1 ∈ K) := by
  classical
  set iota : (Fin 4 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun z => !![z 0, z 2; z 3, z 1]
      map_add' := by intro y z; ext i j; fin_cases i <;> fin_cases j <;> simp
      map_smul' := by intro c z; ext i j; fin_cases i <;> fin_cases j <;> simp } with hiota
  have hia : ∀ z : Fin 4 → ℂ, iota z = !![z 0, z 2; z 3, z 1] := fun z => rfl
  set S : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ) := W.map iota with hS
  have hsing : ∀ A ∈ S, A.det = 0 := by
    rintro A ⟨z, hz, rfl⟩
    rw [hia z, Matrix.det_fin_two_of]
    linear_combination hQ z hz
  have hKS : S ≤ Submodule.span ℂ
      {A : Matrix (Fin 2) (Fin 2) ℂ | A ∈ S ∧ ∀ i j, A i j ∈ K} := by
    rintro A ⟨z, hz, rfl⟩
    have h1 : iota z ∈ Submodule.map iota
        (Submodule.span ℂ {z : Fin 4 → ℂ | z ∈ W ∧ ∀ i, z i ∈ K}) := ⟨z, hK hz, rfl⟩
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro B ⟨y, ⟨hyW, hyK⟩, rfl⟩
    refine ⟨⟨y, hyW, rfl⟩, ?_⟩
    intro i j
    rw [hia y]
    fin_cases i <;> fin_cases j <;> simp [hyK]
  have hNS : iota x ∈ S := ⟨x, hx, rfl⟩
  have hN0 : ∀ i j, (iota x) i j ≠ 0 := by
    intro i j
    rw [hia x]
    fin_cases i <;> fin_cases j <;> simp [hx0 0, hx0 1, hx0 2, hx0 3]
  obtain ⟨-, hcase⟩ :=
    Diaz.rational_singular_subspace_classification hKS hsing hNS hN0
  rcases hcase with ⟨a, haK, ha0, ha⟩ | ⟨b, hbK, hb0, hb⟩
  · obtain ⟨c, hc⟩ := ha _ hNS
    have e00 : x 0 = a 0 * c 0 := by simpa [hia x] using hc 0 0
    have e10 : x 3 = a 1 * c 0 := by simpa [hia x] using hc 1 0
    have e01 : x 2 = a 0 * c 1 := by simpa [hia x] using hc 0 1
    have e11 : x 1 = a 1 * c 1 := by simpa [hia x] using hc 1 1
    have hc0 : c 0 ≠ 0 := by intro h; exact hx0 0 (by rw [e00, h, mul_zero])
    have hc1 : c 1 ≠ 0 := by intro h; exact hx0 2 (by rw [e01, h, mul_zero])
    left
    constructor
    · have : x 0 / x 3 = a 0 / a 1 := by
        rw [e00, e10]; field_simp
      rw [this]; exact div_mem (haK 0) (haK 1)
    · have : x 2 / x 1 = a 0 / a 1 := by
        rw [e01, e11]; field_simp
      rw [this]; exact div_mem (haK 0) (haK 1)
  · obtain ⟨c, hc⟩ := hb _ hNS
    have e00 : x 0 = c 0 * b 0 := by simpa [hia x] using hc 0 0
    have e10 : x 3 = c 1 * b 0 := by simpa [hia x] using hc 1 0
    have e01 : x 2 = c 0 * b 1 := by simpa [hia x] using hc 0 1
    have e11 : x 1 = c 1 * b 1 := by simpa [hia x] using hc 1 1
    have hc0 : c 0 ≠ 0 := by intro h; exact hx0 0 (by rw [e00, h, zero_mul])
    have hc1 : c 1 ≠ 0 := by intro h; exact hx0 3 (by rw [e10, h, zero_mul])
    right
    constructor
    · have : x 0 / x 2 = b 0 / b 1 := by
        rw [e00, e01]; field_simp
      rw [this]; exact div_mem (hbK 0) (hbK 1)
    · have : x 3 / x 1 = b 0 / b 1 := by
        rw [e10, e11]; field_simp
      rw [this]; exact div_mem (hbK 0) (hbK 1)
