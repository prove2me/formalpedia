-- Prove2me | solution 1 for BunkbedAux.xc_and_A_weight
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T02:18:40.666278+00:00
-- url     : https://prove2.me/submissions/d457b4df-2c06-46d1-a6c8-0404afaff972

import Definitions.Def_BunkbedWZRefined
open Bunkbed Bunkbed.Hyper Bunkbed.Hyper.WZExt Finset

private lemma wz_sum {M : Type*} [AddCommMonoid M] (f : WZ → M) :
    ∑ s : WZ, f s = f .abc + f .ab_c + f .ac_b + f .a_bc + f .a_b_c := by
  show Finset.sum {WZ.abc, WZ.ab_c, WZ.ac_b, WZ.a_bc, WZ.a_b_c} f = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-- A block of configurations all of whose entries lie in a fixed set `S` has total weight
`(∑_{q ∈ S} wt q) ^ 6`. -/
private lemma block_weight (P : WZ → ℚ) (S : Finset WZExt) :
    ∑ Ψ ∈ univ.filter (fun Ψ : Fin 6 → WZExt => ∀ h, Ψ h ∈ S), ∏ h, wt P (Ψ h)
      = (∑ q ∈ S, wt P q) ^ 6 := by
  have hset : univ.filter (fun Ψ : Fin 6 → WZExt => ∀ h, Ψ h ∈ S)
      = Fintype.piFinset (fun _ : Fin 6 => S) := by
    ext Ψ; simp [Fintype.mem_piFinset]
  rw [hset, ← Finset.prod_univ_sum]
  simp [Finset.prod_const]

theorem solution (P : WZ → ℚ)
    (hsum : P .abc + P .a_b_c + P .a_bc + P .ab_c + P .ac_b = 1) :
    (∑ Ψ ∈ univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ univ.filter (fun q : WZExt => legal q = true ∧ inLamSq q = false)),
        ∏ h, wt P (Ψ h))
      = (2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b) + 2 * P .a_bc - P .a_bc * P .a_bc) ^ 6
    ∧ (∑ Ψ ∈ univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ ({Sum.inr 1, Sum.inr 3} : Finset WZExt)), ∏ h, wt P (Ψ h))
      = (2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b)) ^ 6 := by
  constructor
  · rw [block_weight]
    congr 1
    rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [wz_sum, Fin.sum_univ_four, wt, toPair, legal, inLamSq]
    simp +decide
    linear_combination (2 * P WZ.a_bc) * hsum
  · rw [block_weight]
    congr 1
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [wt]; ring
