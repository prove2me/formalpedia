-- Prove2me | solution 1 for BunkbedAux.xc_weight
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T01:27:22.801918+00:00
-- url     : https://prove2.me/submissions/9549adf4-9468-4f35-b5dd-0fbc6bf5460e

import Definitions.Def_BunkbedWZRefined
open Bunkbed.Hyper Bunkbed.Hyper.WZExt Finset

private lemma wz_sum {M : Type*} [AddCommMonoid M] (f : WZ → M) :
    ∑ s : WZ, f s = f .abc + f .ab_c + f .ac_b + f .a_bc + f .a_b_c := by
  show Finset.sum {WZ.abc, WZ.ab_c, WZ.ac_b, WZ.a_bc, WZ.a_b_c} f = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

theorem solution (P : WZ → ℚ)
    (hsum : P .abc + P .a_b_c + P .a_bc + P .ab_c + P .ac_b = 1) :
    (∑ q ∈ univ.filter (fun q : WZExt => legal q = true ∧ inLamSq q = false), wt P q)
      = 2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b) + 2 * P .a_bc - P .a_bc * P .a_bc
    ∧ (wt P (Sum.inr 1) + wt P (Sum.inr 3))
      = 2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b) := by
  refine ⟨?_, by simp only [wt]; ring⟩
  rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [wz_sum, Fin.sum_univ_four, wt, toPair, legal, inLamSq]
  simp +decide
  linear_combination (2 * P WZ.a_bc) * hsum
