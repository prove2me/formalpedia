-- Prove2me | solution 1 for DiazModulus.six_exponentials
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T11:14:13.859335+00:00
-- url     : https://prove2.me/submissions/b4ee3ac8-f5d4-4a50-8a2b-f684cf9cdf79

import Theorems.Thm_SX_six_exponentials_of_numberField

/-! # Assembly check: the target from rung 2.  Must contain no `sorry`. -/

open Complex ComplexConjugate

theorem solution (x : Fin 2 → ℂ) (y : Fin 3 → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, Transcendental ℚ (Complex.exp (x i * y j)) := by
  classical
  by_contra hcon
  simp only [Transcendental, not_exists, not_not] at hcon
  set S : Set ℂ := Set.range (fun q : Fin 2 × Fin 3 => Complex.exp (x q.1 * y q.2)) with hS
  have hSfin : S.Finite := Set.finite_range _
  haveI : Finite S := hSfin.to_subtype
  have hint : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro z ⟨q, rfl⟩
    exact (hcon q.1 q.2).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin hint
  obtain ⟨i, j, hij⟩ :=
    SX.six_exponentials_of_numberField (d := 2) (l := 3) (by omega) x y hx hy
      (IntermediateField.adjoin ℚ S)
  exact hij (IntermediateField.subset_adjoin ℚ S ⟨(i, j), rfl⟩)

