-- Prove2me | solution 1 for DiazModulus.fischler_theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-21T08:57:57.850185+00:00
-- url     : https://prove2.me/submissions/295cda53-770a-4283-9ce7-1d82ba4c973a

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_strong_six_exponentials_unconditional

open Complex ComplexConjugate

/-! # Fischler 2001, Theorem 2.3

Fischler 2001, Theorem 2.3 (p. 171): the `d × l` form of Roy 1992, Corollary 2 (p. 38, printed for `2 × 3`).
Let `M` be a `d × l` matrix of rank one, `d ≥ 2`, `l ≥ 3`, with entries in `ℒ̃`. Its column space is a line
`ℂu`, so every column is `cⱼ u` and `M i j = uᵢ cⱼ`. If the rows of `M` are free over `Q̄`, so is `u`: a relation
`Σ βᵢ uᵢ = 0` with algebraic `βᵢ` gives `Σ βᵢ (row i) = 0`, since row `i` is `uᵢ c`. In the same way, if the columns
are free over `Q̄`, so is `c`. Suppose both are free. Then `x = (u₀, u₁)` and `y = (c₀, c₁, c₂)` are free over `Q̄`
(sub-families of free families), and every product `xᵢ yⱼ = M i j` lies in `ℒ̃`. This contradicts the strong six
exponentials theorem in its product form. -/

namespace RC10_Fis23
open DiazModulus

/-- A rank-one complex matrix is a product `M i j = cⱼ uᵢ`. -/
theorem rank_one_factor {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ) (hrank : M.rank = 1) :
    ∃ (u : Fin d → ℂ) (c : Fin l → ℂ), ∀ i j, M i j = c j * u i := by
  have hcol : ∀ j, (fun i => M i j) ∈ LinearMap.range M.mulVecLin := fun j =>
    LinearMap.mem_range.2 ⟨Pi.single j 1, by
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]; rfl⟩
  rw [Matrix.rank, finrank_eq_one_iff'] at hrank
  obtain ⟨w, -, hw⟩ := hrank
  choose c hc using fun j => hw ⟨_, hcol j⟩
  refine ⟨w, c, fun i j => ?_⟩
  have := congrArg (fun z : LinearMap.range M.mulVecLin => (z : Fin d → ℂ) i) (hc j)
  simpa using this.symm

/-- If the family `i ↦ (uᵢ cⱼ)ⱼ` is free over `Q̄`, then so is `u`. -/
theorem linInd_of_mul {ι κ : Type*} (u : ι → ℂ) (c : κ → ℂ)
    (h : LinearIndependent (↥Qbar) (fun i => fun j => c j * u i)) : LinearIndependent (↥Qbar) u := by
  let f : ℂ →ₗ[↥Qbar] (κ → ℂ) :=
    { toFun := fun z j => c j * z
      map_add' := fun a b => by funext j; simp [mul_add]
      map_smul' := fun r z => by funext j; simp }
  exact LinearIndependent.of_comp f h

end RC10_Fis23

open DiazModulus RC10_Fis23 in
theorem solution {d l : ℕ} (hd : 2 ≤ d) (hl : 3 ≤ l) (M : Matrix (Fin d) (Fin l) ℂ)
    (hrank : M.rank = 1) (hM : ∀ i j, M i j ∈ LogAlgTilde) :
    ¬ LinearIndependent (↥Qbar) (fun i => M i) ∨
      ¬ LinearIndependent (↥Qbar) (fun j => fun i => M i j) := by
  obtain ⟨u, c, huc⟩ := rank_one_factor M hrank
  rw [or_iff_not_imp_left, not_not]
  intro hr hcol
  have er : (fun i => fun j => c j * u i) = fun i => M i := by
    funext i j; exact (huc i j).symm
  have ec : (fun j => fun i => u i * c j) = fun j => fun i => M i j := by
    funext j i; rw [huc, mul_comm]
  have hu : LinearIndependent (↥Qbar) u := linInd_of_mul u c (er ▸ hr)
  have hc : LinearIndependent (↥Qbar) c := linInd_of_mul c u (ec ▸ hcol)
  refine DiazModulus.strong_six_exponentials_unconditional (u ∘ Fin.castLE hd) (c ∘ Fin.castLE hl)
    (hu.comp _ (Fin.castLE_injective hd)) (hc.comp _ (Fin.castLE_injective hl)) fun i j => ?_
  simp only [Function.comp_apply]
  rw [mul_comm, ← huc]
  exact hM _ _
