-- Prove2me | solution 1 for DiazModulus.variations_cor_3_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:32:37.569216+00:00
-- url     : https://prove2.me/submissions/d5b00e0d-468c-467f-9b1a-c5ba1dafd7ac

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_variations_hyperplane_bound

open Complex ComplexConjugate

/-! # Waldschmidt's Corollary 3.2 of *Variations*

Let `M = (Λ_{ij})` be an `m × ℓ` matrix with entries in `ℒ̃` and `Q̄`-free columns, let `x₁, …, x_m ∈ ℂ` be
`Q̄`-free, and suppose `Σᵢ xᵢΛ_{ij} = 0` for every `j`, with `ℓ > m(m − 1)`. If `m = 0`, the columns are `ℓ > 0`
vectors of the zero space, which cannot be free. If `m ≥ 1`, `x₁ ≠ 0`, so the form `ψ(z) = Σᵢ xᵢzᵢ` is onto
`ℂ` and its kernel `V` is a hyperplane of `ℂ^m`. An algebraic `z ∈ V` is a `Q̄`-relation `Σᵢ zᵢxᵢ = 0`, so
`z = 0`: `V` contains no nonzero algebraic vector. The columns of `M` lie in `V`, have coordinates in `ℒ̃` and
are `Q̄`-free, so `ℓ ≤ dim_Q̄ (V ∩ ℒ̃^m) ≤ m(m − 1)` by the bound for hyperplanes (*Variations* Th. 3.1), a
contradiction. -/

namespace RC2_C32
open DiazModulus

/-- The linear form `z ↦ Σᵢ xᵢzᵢ`. -/
noncomputable def linForm {m : ℕ} (x : Fin m → ℂ) : (Fin m → ℂ) →ₗ[ℂ] ℂ where
  toFun z := ∑ i, x i * z i
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem linForm_apply {m : ℕ} (x : Fin m → ℂ) (z : Fin m → ℂ) : linForm x z = ∑ i, x i * z i := rfl

end RC2_C32

open DiazModulus RC2_C32 in
theorem solution {m ℓ : ℕ} (M : Matrix (Fin m) (Fin ℓ) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hcol : LinearIndependent (↥Qbar) M.col) (x : Fin m → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hℓ : m * (m - 1) < ℓ) :
    ∃ j : Fin ℓ, ∑ i, x i * M i j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- the columns are `ℓ > 0` vectors of the zero space
    exact hcol.ne_zero ⟨0, by omega⟩ (Subsingleton.elim _ _)
  let V := LinearMap.ker (linForm x)
  have hx0 : x ⟨0, hm⟩ ≠ 0 := hx.ne_zero _
  have hsurj : Function.Surjective (linForm x) := by
    intro w
    refine ⟨Pi.single ⟨0, hm⟩ (w / x ⟨0, hm⟩), ?_⟩
    simp [linForm_apply, Pi.single_apply]
    field_simp
  have hdim : Module.finrank ℂ ↥V + 1 = m := by
    have h := LinearMap.finrank_range_add_finrank_ker (linForm x)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at h
    simp only [V]; omega
  have hVQ : ∀ v ∈ V, (∀ i, v i ∈ Qbar) → v = 0 := by
    intro v hv hvQ
    have hv0 : ∑ i, x i * v i = 0 := hv
    have key := (Fintype.linearIndependent_iff.mp hx) (fun i => ⟨v i, hvQ i⟩) (by
      simp only [Subfield.smul_def, smul_eq_mul]
      rw [← hv0]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
    funext i
    simpa using congrArg Subtype.val (key i)
  obtain ⟨hfin, hbound⟩ := DiazModulus.variations_hyperplane_bound V hdim hVQ
  have hcolV : ∀ j, M.col j ∈ V := by
    intro j
    show ∑ i, x i * M.col j i = 0
    simpa [Matrix.col_apply] using hcon j
  let W := V.restrictScalars (↥Qbar) ⊓ Submodule.pi Set.univ (fun _ : Fin m => LogAlgTilde)
  let cW : Fin ℓ → ↥W :=
    fun j => ⟨M.col j, hcolV j, fun i _ => by simpa [Matrix.col_apply] using hM i j⟩
  have hcW : LinearIndependent (↥Qbar) cW := LinearIndependent.of_comp W.subtype hcol
  have hcard := hcW.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  have := le_trans hcard hbound
  omega
