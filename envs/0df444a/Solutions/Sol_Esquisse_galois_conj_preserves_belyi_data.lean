-- Prove2me | solution 1 for Esquisse.galois_conj_preserves_belyi_data
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T00:06:14.086726+00:00
-- url     : https://prove2.me/submissions/bf8664b7-85fd-40e5-9a01-bc1386f98a04

import Definitions.Def_esquisse_dessins_basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots

open Polynomial
open Esquisse

theorem solution (γ : GaloisQ) (P : Polynomial AlgNum)
    (hP : IsBelyiPolynomial P) :
    IsBelyiPolynomial (galoisConj γ P) ∧ (galoisConj γ P).natDegree = P.natDegree ∧
      ∀ c z : AlgNum, (P - C c).rootMultiplicity z
        = (galoisConj γ P - C (γ c)).rootMultiplicity (γ z) := by
  have hd : (galoisConj γ P).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (f := γ.toAlgHom.toRingHom) γ.injective P
  have heval (Q : Polynomial AlgNum) (z : AlgNum) :
      (galoisConj γ Q).eval (γ z) = γ (Q.eval z) := by
    exact Polynomial.eval_map_apply γ.toAlgHom.toRingHom z
  refine ⟨⟨by simpa [hd] using hP.1, ?_⟩, hd, ?_⟩
  · intro w hw
    obtain ⟨z, rfl⟩ := γ.surjective w
    have hz : P.derivative.eval z = 0 := by
      have hw' : (galoisConj γ P.derivative).eval (γ z) = 0 := by
        simpa only [galoisConj, Polynomial.derivative_map] using hw
      apply γ.injective
      calc
        γ (P.derivative.eval z) = (galoisConj γ P.derivative).eval (γ z) :=
          (heval P.derivative z).symm
        _ = 0 := hw'
        _ = γ 0 := (map_zero γ).symm
    rcases hP.2 z hz with hz0 | hz1
    · left
      rw [heval, hz0, map_zero]
    · right
      rw [heval, hz1, map_one]
  · intro c z
    simpa [galoisConj] using
      (Polynomial.eq_rootMultiplicity_map (p := P - C c)
        (f := γ.toAlgHom.toRingHom) γ.injective z)
