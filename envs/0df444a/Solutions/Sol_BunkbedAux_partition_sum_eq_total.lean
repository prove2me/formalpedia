-- Prove2me | solution 1 for BunkbedAux.partition_sum_eq_total
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T18:39:26.176744+00:00
-- url     : https://prove2.me/submissions/46320563-4de8-4ac8-a8d9-d7c7650b57f0

import Definitions.Def_BunkbedPercolation

open Bunkbed Finset

/-- Pointwise: for a fixed open edge set `S`, exactly one of the five partition events of the
triple `(a, b, c)` holds, so the five indicator terms add up to the plain weight. -/
private lemma pointwise {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) (a b c : V) (S : Finset (Sym2 V)) :
    ((if (ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c then weight E w S else 0)
      + (if (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable a c then weight E w S else 0)
      + (if (ofEdges S).Reachable a c ∧ ¬ (ofEdges S).Reachable a b then weight E w S else 0)
      + (if (ofEdges S).Reachable b c ∧ ¬ (ofEdges S).Reachable a b then weight E w S else 0)
      + (if ¬ (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable b c ∧
            ¬ (ofEdges S).Reachable a c then weight E w S else 0))
      = weight E w S := by
  by_cases p : (ofEdges S).Reachable a b
  · by_cases q : (ofEdges S).Reachable b c
    · have r : (ofEdges S).Reachable a c := p.trans q
      simp [p, q, r]
    · have r : ¬ (ofEdges S).Reachable a c := fun h => q (p.symm.trans h)
      simp [p, q, r]
  · by_cases q : (ofEdges S).Reachable b c
    · have r : ¬ (ofEdges S).Reachable a c := fun h => p (h.trans q.symm)
      simp [p, q, r]
    · by_cases r : (ofEdges S).Reachable a c
      · simp [p, q, r]
      · simp [p, q, r]

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) (a b c : V) :
    Pabc E w a b c + Pab_c E w a b c + Pac_b E w a b c + Pa_bc E w a b c + Pa_b_c E w a b c
      = ∑ S ∈ E.powerset, weight E w S := by
  unfold Pabc Pab_c Pac_b Pa_bc Pa_b_c probOf
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => pointwise E w a b c S
