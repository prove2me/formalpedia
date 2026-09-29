-- Prove2me | solution 1 for BraidsLinksMCG.cor_1_8_4_center_braid_group
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-14T12:09:45.207429+00:00
-- url     : https://prove2.me/submissions/57ec025b-63ed-4c2b-902c-134742dcbaf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_braid_exponent_sum_hom
import Theorems.Thm_BraidsLinksMCG_cor_1_8_4_center_eq

open BraidsLinksMCG in
theorem solution (n : ℕ) (hn : 3 ≤ n) :
    Subgroup.center (ArtinBraidGroup n) = Subgroup.zpowers (sigmaProd n ^ n) ∧
      ¬ IsOfFinOrder (sigmaProd n ^ n) := by
  refine ⟨cor_1_8_4_center_eq n hn, ?_⟩
  obtain ⟨eps, heps⟩ := braid_exponent_sum_hom n
  have hprod : eps (sigmaProd n) = Multiplicative.ofAdd ((n - 1 : ℕ) : ℤ) := by
    simp only [sigmaProd, map_list_prod, List.map_ofFn]
    rw [show (⇑eps ∘ fun i : Fin (n - 1) => sigma i)
        = (fun _ : Fin (n - 1) => Multiplicative.ofAdd (1 : ℤ)) from funext heps,
      List.ofFn_const, List.prod_replicate, ← ofAdd_nsmul]
    congr 1
    simp
  have hpow : eps (sigmaProd n ^ n) = Multiplicative.ofAdd ((n * (n - 1) : ℕ) : ℤ) := by
    rw [map_pow, hprod, ← ofAdd_nsmul]
    congr 1
  intro hfin
  obtain ⟨m, hm, hmeq⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have h2 : (eps (sigmaProd n ^ n)) ^ m = 1 := by rw [← map_pow, hmeq, map_one]
  rw [hpow, ← ofAdd_nsmul] at h2
  have h3 := congrArg Multiplicative.toAdd h2
  simp at h3
  omega
