-- Prove2me | solution 1 for D1Bound5.exists_mixed_symmetric_root_matrix_with_roots
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:41:11.217083+00:00
-- url     : https://prove2.me/submissions/b40fd12f-c7e4-4f21-9bf9-f3ca4dbc4887

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_exists_mixed_symmetric_root_matrix

section
namespace D1Bound5

















end D1Bound5
namespace D1Bound5



/-- Also choose the four complex square roots, preserving the integral
symmetric matrix and the exact root-square equations. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a : Fin 4 → R) (M : Matrix (Fin 4) (Fin 4) R)
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      3 ≤ ‖f (a i) * f (a j)‖)
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      9 ≤ ‖f (a i) * f (a j)‖) :
    ∃ (u : Fin 4 → ℂ) (S : Matrix (Fin 4) (Fin 4) R),
      (∀ i, (u i)^2 = f (a i)) ∧
      (∀ i, S i i = a i) ∧
      (∀ i j, S i j = S j i) ∧
      (∀ i j, i ≠ j → S i j = M i j ∨ S i j = -M i j) ∧
      (∀ i j, i ≠ j → (S i j)^2 = a i * a j + 1) ∧
      (∀ i j, i ≠ j → MixedSignedEntryGood f a u i j (S i j)) := by
  classical
  have hr (i : Fin 4) : ∃ z : ℂ, z^2 = f (a i) :=
    IsAlgClosed.exists_pow_nat_eq (f (a i)) (by decide : 0 < 2)
  let u : Fin 4 → ℂ := fun i => Classical.choose (hr i)
  have hu (i : Fin 4) : (u i)^2 = f (a i) := Classical.choose_spec (hr i)
  obtain ⟨S, hd, hs, hsgn, hsq, hnear⟩ :=
    exists_mixed_symmetric_root_matrix f a u M hu hdiag hsymm hroot hfirst hlater
  exact ⟨u, S, hu, hd, hs, hsgn, hsq, hnear⟩

end D1Bound5
end
