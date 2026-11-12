-- Prove2me | solution 1 for BunkbedAux.Pabc_add_Pab_c_eq_connProb
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T18:39:26.801817+00:00
-- url     : https://prove2.me/submissions/98c61279-763c-41e1-84b4-91981cedbf70

import Definitions.Def_BunkbedPercolation

open Bunkbed Finset

/-- Pointwise splitting of the event `R a b` according to the status of `c`. -/
private lemma split_pointwise {V : Type*} [Fintype V] [DecidableEq V]
    (w : Sym2 V → ℚ) (E S : Finset (Sym2 V)) (a b c : V) :
    ((if (ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c then weight E w S else 0)
        + (if (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable a c then weight E w S else 0))
      = (if (ofEdges S).Reachable a b then weight E w S else 0) := by
  by_cases hab : (ofEdges S).Reachable a b
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : (ofEdges S).Reachable a c := hab.trans hbc
      simp [hab, hbc, hac]
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hbc (hab.symm.trans h)
      simp [hab, hbc, hac]
  · simp [hab]

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) (a b c : V) :
    Pabc E w a b c + Pab_c E w a b c = connProb E w a b := by
  unfold Pabc Pab_c connProb probOf
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => split_pointwise w E S a b c
