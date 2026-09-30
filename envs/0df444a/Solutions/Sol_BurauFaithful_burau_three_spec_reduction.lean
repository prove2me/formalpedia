-- Prove2me | solution 1 for BurauFaithful.burau_three_spec_reduction
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-29T17:21:07.243821+00:00
-- url     : https://prove2.me/submissions/1641f336-f83a-486e-a137-363e9f5e3ee5

/-
`BurauFaithful.burau_three_spec_reduction`: after specializing at `t = -1`, the unreduced 3×3 Burau
representation of `B₃` is conjugate, over `ℤ`, to the direct sum of the trivial representation and
the 2×2 reduced Burau representation.

The unreduced representation fixes the vector `v = (1,1,1)` and the covector `w = (1,t,t²)`, and
`w·v = 1 + t + t²`, which is `1 ≠ 0` at `t = -1`; hence the decomposition splits at `t = -1`. The
basis `C = [v | (t,-1,0) | (t²,0,-1)]` evaluated at `t = -1` is `!![1,-1,1; 1,-1,0; 1,0,-1]`, of
determinant `1 + t + t² = 1` (Birman, §3.3, Theorem 3.15, pp. 129-130).
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open LaurentPolynomial Matrix BraidsLinksMCG

/-- The specialization `ℤ[t,t⁻¹] → ℤ`, `t ↦ -1`. -/
noncomputable def specM1 : (LaurentPolynomial ℤ) →+* ℤ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ)

/-- The conjugating matrix at `t = -1`, i.e. `!![1,t,t²; 1,-1,0; 1,0,-1]` evaluated there. -/
def Cneg : Matrix (Fin 3) (Fin 3) ℤ := !![1, -1, 1; 1, -1, 0; 1, 0, -1]

theorem solution :
    ((Matrix.GeneralLinearGroup.map specM1
          (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩)) :
        Matrix (Fin 3) (Fin 3) ℤ) * Cneg =
      Cneg * !![1, 0, 0; 0, 1, -1; 0, 0, 1]) ∧
    ((Matrix.GeneralLinearGroup.map specM1
          (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩)) :
        Matrix (Fin 3) (Fin 3) ℤ) * Cneg =
      Cneg * !![1, 0, 0; 0, 2, -1; 0, 1, 0]) := by
  have hg : ∀ i : Fin (3 - 1),
      (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma i)).1 = BurauFaithful.burauMatrix i := by
    intro i
    have hh := PresentedGroup.toGroup.of (h := BurauFaithful.burauGen_relations 3) (x := i)
    exact congrArg Units.val hh
  have hspec : ∀ i : Fin (3 - 1),
      (Matrix.GeneralLinearGroup.map specM1
          (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma i)) :
        Matrix (Fin 3) (Fin 3) ℤ) = Matrix.map (BurauFaithful.burauMatrix i) specM1 := by
    intro i
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rw [hg i]
    rfl
  have hmat0 : (Matrix.map (BurauFaithful.burauMatrix (0 : Fin 2)) specM1 :
      Matrix (Fin 3) (Fin 3) ℤ) = !![2, -1, 0; 1, 0, 0; 0, 0, 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [BurauFaithful.burauMatrix_apply, specM1, LaurentPolynomial.eval₂_T,
        Matrix.map_apply] <;> norm_num
  have hmat1 : (Matrix.map (BurauFaithful.burauMatrix (1 : Fin 2)) specM1 :
      Matrix (Fin 3) (Fin 3) ℤ) = !![1, 0, 0; 0, 2, -1; 0, 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [BurauFaithful.burauMatrix_apply, specM1, LaurentPolynomial.eval₂_T,
        Matrix.map_apply] <;> norm_num
  have h0 : (Matrix.GeneralLinearGroup.map specM1
      (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩)) :
      Matrix (Fin 3) (Fin 3) ℤ) = !![2, -1, 0; 1, 0, 0; 0, 0, 1] :=
    (hspec 0).trans hmat0
  have h1 : (Matrix.GeneralLinearGroup.map specM1
      (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩)) :
      Matrix (Fin 3) (Fin 3) ℤ) = !![1, 0, 0; 0, 2, -1; 0, 1, 0] :=
    (hspec 1).trans hmat1
  constructor
  · rw [h0]
    decide
  · rw [h1]
    decide
