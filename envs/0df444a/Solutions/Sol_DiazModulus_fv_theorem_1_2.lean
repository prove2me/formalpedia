-- Prove2me | solution 1 for DiazModulus.fv_theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:34:46.332204+00:00
-- url     : https://prove2.me/submissions/a6b2094a-13e2-43a8-96aa-c9d5efeb7183

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_fv_theorem_2_1
import Theorems.Thm_DiazModulus_fv_two_by_three_lines

open Complex ComplexConjugate

/-! # Three 2 × 2 minors, one of them outside `ℒ̃`

Let `v` be the five columns of `(I₂, M)` and `X` their `Q̄`-span, of dimension 5 since the columns are
`Q̄`-free. Let `J(z₀, z₁) = (−z₁, z₀)` and `Y = J(X)`, also of dimension 5. For two vectors of `ℂ²`,
`x · J(x′) = x₁x′₀ − x₀x′₁` is a determinant, so on the generators the products `vₖ · J(vₖ′)` are `0`,
`±1`, `±Mᵢⱼ` or `±` one of the three minors. If all three minors lie in `ℒ̃`, every `vₖ · J(vₖ′)` does, and
by bilinearity (`ℒ̃` is a `Q̄`-space containing `1` and the entries of `M`) so does every `x · y` with
`x ∈ X`, `y ∈ Y`. On the other hand Theorem 2.1 applies with `n = 2`, `dim X = 5`: for `V = 0` the
required inequality is `10 < 15`; for a line `V`, `J` maps `X ∩ J⁻¹(V)` onto `Y ∩ V`, and `J⁻¹(V)` is a
line, so `dim(Y ∩ V) ≤ 3` by the bound for lines, and the inequality is `5 < 3·(5 − 3)`. Theorem 2.1
gives `x ∈ X`, `y ∈ Y` with `x · y ∉ ℒ̃`, a contradiction. -/

namespace RC3_A7
open DiazModulus

/-- The rotation `J(z₀, z₁) = (−z₁, z₀)`. -/
def J : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun z := ![-z 1, z 0]
  invFun z := ![z 1, -z 0]
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' c x := by ext i; fin_cases i <;> simp
  left_inv z := by ext i; fin_cases i <;> simp
  right_inv z := by ext i; fin_cases i <;> simp

theorem dot_J (x z : Fin 2 → ℂ) : x ⬝ᵥ J z = x 1 * z 0 - x 0 * z 1 := by
  simp [J, dotProduct, Fin.sum_univ_two]; ring

/-- Dot product with a fixed vector on the left, as a `Q̄`-linear map. -/
def dotL (w : Fin 2 → ℂ) : (Fin 2 → ℂ) →ₗ[↥Qbar] ℂ where
  toFun x := w ⬝ᵥ x
  map_add' x y := dotProduct_add w x y
  map_smul' c x := dotProduct_smul c w x

/-- Dot product with a fixed vector on the right, as a `Q̄`-linear map. -/
def dotR (w : Fin 2 → ℂ) : (Fin 2 → ℂ) →ₗ[↥Qbar] ℂ where
  toFun x := x ⬝ᵥ w
  map_add' x y := add_dotProduct x y w
  map_smul' c x := smul_dotProduct c x w

theorem span_mem {ι : Type*} (φ : (Fin 2 → ℂ) →ₗ[↥Qbar] ℂ) (v : ι → Fin 2 → ℂ)
    (h : ∀ k, φ (v k) ∈ LogAlgTilde) :
    ∀ x ∈ Submodule.span (↥Qbar) (Set.range v), φ x ∈ LogAlgTilde := fun _ hx =>
  (Submodule.span_le.mpr (Set.range_subset_iff.mpr h) :
    Submodule.span (↥Qbar) (Set.range v) ≤ LogAlgTilde.comap φ) hx

theorem one_mem_tilde : (1 : ℂ) ∈ LogAlgTilde :=
  Submodule.subset_span (Set.mem_insert _ _)

end RC3_A7

open DiazModulus RC3_A7 in
theorem solution (M : Matrix (Fin 2) (Fin 3) ℂ) (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hrows : LinearIndependent (↥Qbar) (Matrix.fromRows M (1 : Matrix (Fin 3) (Fin 3) ℂ)).row)
    (hcols : LinearIndependent (↥Qbar) (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col) :
    M 0 1 * M 1 2 - M 0 2 * M 1 1 ∉ LogAlgTilde ∨
      M 0 2 * M 1 0 - M 0 0 * M 1 2 ∉ LogAlgTilde ∨
      M 0 0 * M 1 1 - M 0 1 * M 1 0 ∉ LogAlgTilde := by
  set v := (Matrix.fromCols (1 : Matrix (Fin 2) (Fin 2) ℂ) M).col with hv
  set X := Submodule.span (↥Qbar) (Set.range v) with hX
  have : FiniteDimensional (↥Qbar) X := FiniteDimensional.span_of_finite _ (Set.finite_range v)
  set J' : (Fin 2 → ℂ) ≃ₗ[↥Qbar] (Fin 2 → ℂ) := J.restrictScalars (↥Qbar) with hJ'
  set Y := X.map (J' : (Fin 2 → ℂ) →ₗ[↥Qbar] (Fin 2 → ℂ)) with hY
  have hX5 : Module.finrank (↥Qbar) X = 5 := by rw [hX, finrank_span_eq_card hcols]; simp
  have hY5 : Module.finrank (↥Qbar) Y = 5 := by rw [hY, LinearEquiv.finrank_map_eq, hX5]
  -- the bound for proper subspaces
  have hμ : ∀ V : Submodule ℂ (Fin 2 → ℂ), V ≠ ⊤ →
      Module.finrank (↥Qbar) ↥X * (2 - Module.finrank ℂ ↥V) <
        (Module.finrank (↥Qbar) ↥X - 2) *
          (Module.finrank (↥Qbar) ↥Y - Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar))) := by
    intro V hV
    rw [hX5, hY5]
    have hV2 : Module.finrank ℂ V ≤ 2 := by have := Submodule.finrank_le V; simpa using this
    have hV2' : Module.finrank ℂ V ≠ 2 := fun h =>
      hV (Submodule.eq_top_of_finrank_eq (by simpa using h))
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ V) with h0 | hpos
    · rw [Submodule.finrank_eq_zero.mp h0, Submodule.restrictScalars_bot, inf_bot_eq]
      simp only [finrank_bot]
      omega
    · set W := V.comap (J : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) with hW
      have hWtop : W ≠ ⊤ := by
        intro hWt; apply hV; rw [eq_top_iff]; intro z _
        have : J.symm z ∈ W := hWt ▸ Submodule.mem_top
        rw [hW, Submodule.mem_comap] at this
        simpa using this
      have hA6 := DiazModulus.fv_two_by_three_lines M hrows W hWtop
      have hle : Y ⊓ V.restrictScalars (↥Qbar) ≤
          (X ⊓ W.restrictScalars (↥Qbar)).map (J' : (Fin 2 → ℂ) →ₗ[↥Qbar] (Fin 2 → ℂ)) := by
        rintro y ⟨hyY, hyV⟩
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hyY
        exact Submodule.mem_map_of_mem ⟨hx, hyV⟩
      have ht : Module.finrank (↥Qbar) ↥(Y ⊓ V.restrictScalars (↥Qbar)) ≤ 3 :=
        (Submodule.finrank_mono hle).trans (by rw [LinearEquiv.finrank_map_eq]; exact hA6)
      omega
  obtain ⟨x, hx, y, hy, hxy⟩ := DiazModulus.fv_theorem_2_1 X Y (by omega) hμ
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hy
  apply hxy
  -- the twenty-five generator values
  have hgen : ∀ k k', v k ⬝ᵥ J (v k') ∈ LogAlgTilde := by
    intro k k'
    rw [dot_J]
    rcases k with i | j <;> rcases k' with i' | j' <;>
      [fin_cases i <;> fin_cases i'; fin_cases i <;> fin_cases j'; fin_cases j <;> fin_cases i';
        fin_cases j <;> fin_cases j'] <;>
      simp [hv] <;>
      first
      | exact zero_mem _
      | (convert zero_mem LogAlgTilde using 1; ring1)
      | exact one_mem_tilde
      | exact neg_mem one_mem_tilde
      | exact hM _ _
      | exact neg_mem (hM _ _)
      | (convert h1 using 1; ring1)
      | (convert neg_mem h1 using 1; ring1)
      | (convert h2 using 1; ring1)
      | (convert neg_mem h2 using 1; ring1)
      | (convert h3 using 1; ring1)
      | (convert neg_mem h3 using 1; ring1)
  have hstep : ∀ k, ∀ z ∈ X, v k ⬝ᵥ J z ∈ LogAlgTilde := fun k =>
    span_mem ((dotL (v k)).comp (J' : (Fin 2 → ℂ) →ₗ[↥Qbar] (Fin 2 → ℂ))) v (hgen k)
  exact span_mem (dotR (J x')) v (fun k => hstep k x' hx') x hx
