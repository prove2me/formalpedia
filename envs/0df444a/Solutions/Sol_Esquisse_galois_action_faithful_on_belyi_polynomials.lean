-- Prove2me | solution 1 for Esquisse.galois_action_faithful_on_belyi_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T00:50:18.953727+00:00
-- url     : https://prove2.me/submissions/5fc5c29f-cb2d-4eb2-8bb0-000a28b4b5e7

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Derivative
import Definitions.Def_esquisse_dessins_basic
import Theorems.Thm_Esquisse_belyi_polynomial_separating_algebraic_number

open Polynomial

namespace Esquisse

/-- Future reduction to the existing separation target; no construction of the
separating polynomial is asserted in this proof. -/
theorem galois_action_faithful_on_belyi_polynomials (γ : GaloisQ) (hγ : γ ≠ 1) :
    ∃ P : Polynomial AlgNum, IsBelyiPolynomial P ∧
      ¬ AffineEquivalent P (galoisConj γ P) := by
  classical
  have hmoved : ∃ α : AlgNum, γ α ≠ α := by
    by_contra hnone
    apply hγ
    apply AlgEquiv.ext
    intro α
    have hfixed : γ α = α := by
      by_contra hne
      exact hnone ⟨α, hne⟩
    simpa using hfixed
  obtain ⟨α, hα⟩ := hmoved
  obtain ⟨P, hP, hseparates⟩ := belyi_polynomial_separating_algebraic_number α
  exact ⟨P, hP, fun hequiv => hα (hseparates γ hequiv)⟩

end Esquisse

theorem solution (γ : Esquisse.GaloisQ) (hγ : γ ≠ 1) :
    ∃ P : Polynomial Esquisse.AlgNum, Esquisse.IsBelyiPolynomial P ∧
      ¬ Esquisse.AffineEquivalent P (Esquisse.galoisConj γ P) :=
  Esquisse.galois_action_faithful_on_belyi_polynomials γ hγ

#print axioms solution
