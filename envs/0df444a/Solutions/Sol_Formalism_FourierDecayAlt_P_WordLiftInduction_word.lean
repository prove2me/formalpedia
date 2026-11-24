-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordLiftInduction.word
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:31.244657+00:00
-- url     : https://prove2.me/submissions/824e24d1-e973-4991-8af9-a71abe296c09

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordLiftInduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_head_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordLiftInduction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
namespace Formalism.FourierDecayAlt.P.WordLiftInduction
theorem _root_.solution (Ξ : Sesq M) (d : ℕ) (X X' : M) : ∀ (K : ℕ) (dat : Fin K → Dat R) (c : Fin K → ℂ)
    (grid : Fin K → Fin (d + 1) → ℝ),
    (∀ a (Q Q' : R), ∑ i, ((lagCo (grid a) i : ℝ) : ℂ) *
      one Ξ (dat a) (grid a i) (Q • X) (Q' • X') = c a * Ξ (Q • X) (Q' • X')) →
    (∏ a, c a) * Ξ X X' =
      ∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) *
        Fw Ξ X X' (List.ofFn fun a => (dat a, grid a (j a))) 1 1 := by
  intro K
  induction K with
  | zero =>
    intro dat c grid _
    simp [Fw]
  | succ K ih =>
    intro dat c grid h
    have ih' := ih (fun a => dat a.succ) (fun a => c a.succ) (fun a => grid a.succ)
      (fun a => h a.succ)
    rw [Fin.prod_univ_succ, mul_assoc, ih', mul_sum,
      ← (Fin.consEquiv (fun _ : Fin (K + 1) => Fin (d + 1))).sum_comp, Fintype.sum_prod_type,
      sum_comm]
    refine sum_congr rfl fun j' _ => ?_
    rw [mul_left_comm, ← head_step Ξ X X' (dat 0) (grid 0) (c 0) (h 0), mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ]
    push_cast
    ring
end Formalism.FourierDecayAlt.P.WordLiftInduction
