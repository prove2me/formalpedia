-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.univariate_and_pair_lconvexity
-- status  : ACCEPTED   (disprove)
-- author  : @sometik179
-- created : 2026-10-02T15:49:01.674844+00:00
-- url     : https://prove2.me/submissions/ed4daf1c-fc89-4751-926f-cc3d5112340d

import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DiscreteConvexUnivariate
import Mathlib.Tactic.NormNum

open DiscreteConvex.LConvexFunctionsB

namespace GapCounterexample
noncomputable def psi (z : ℤ) : WithTop ℝ := if z=0 ∨ z=3 then 0 else ⊤

lemma local_convex : DiscreteConvexUnivariate psi := by
  constructor
  · exact ⟨0, by norm_num [psi]⟩
  · intro x
    have he : psi x + psi (x+2) = ⊤ := by
      simp only [psi]
      split_ifs <;> simp_all <;> omega
    rw [he]
    exact le_top

lemma not_pair : ¬ SBF (fun p : Fin 2 → ℤ => psi (p 0-p 1)) := by
  intro h
  have hh := h (fun i => if i=0 then 3 else 0) (fun _ => 1)
  norm_num [psi, Pi.sup_apply, Pi.inf_apply] at hh
end GapCounterexample

theorem solution : ¬ (∀ (psi : ℤ → WithTop ℝ), DiscreteConvexUnivariate psi →
    LNaturalConvex (fun p : Unit → ℤ => psi (p ())) ∧
    (SBF (fun p : Fin 2 → ℤ => psi (p 0 - p 1)) ∧ TRF (fun p : Fin 2 → ℤ => psi (p 0 - p 1)))) := by
  intro h
  exact GapCounterexample.not_pair (h GapCounterexample.psi GapCounterexample.local_convex).2.1

#print axioms solution
