-- Prove2me | solution 2 for BraidsLinksMCG.cor_1_8_4_center_braid_group
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:04:00.094895+00:00
-- url     : https://prove2.me/submissions/58e8afbc-8523-47f5-93c5-2b6275eeffed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_cor_1_8_4_center_eq
import Theorems.Thm_BraidsLinksMCG_braid_exponent_sum_hom
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

/-- `Multiplicative ℤ` is torsion free. -/
private theorem center_finOrder_int {a : Multiplicative ℤ} (h : IsOfFinOrder a) : a = 1 := by
  rw [isOfFinOrder_iff_pow_eq_one] at h
  obtain ⟨m, hm, hmeq⟩ := h
  have hz : (m : ℤ) * Multiplicative.toAdd a = 0 := by
    have := congrArg Multiplicative.toAdd hmeq
    simpa [nsmul_eq_mul] using this
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact absurd h1 hm0
  · simpa using h2

theorem _root_.solution (n : ℕ) (hn : 3 ≤ n) :
    Subgroup.center (ArtinBraidGroup n) = Subgroup.zpowers (sigmaProd n ^ n) ∧
      ¬ IsOfFinOrder (sigmaProd n ^ n) := by
  refine ⟨BraidsLinksMCG.cor_1_8_4_center_eq n hn, ?_⟩
  obtain ⟨eps, heps⟩ := BraidsLinksMCG.braid_exponent_sum_hom n
  have hsp : eps (sigmaProd n) = Multiplicative.ofAdd ((n - 1 : ℕ) : ℤ) := by
    unfold sigmaProd
    rw [map_list_prod, List.map_ofFn]
    have hfun : (⇑eps ∘ fun i : Fin (n - 1) => sigma i)
        = fun _ : Fin (n - 1) => Multiplicative.ofAdd (1 : ℤ) := funext heps
    rw [hfun, List.ofFn_const, List.prod_replicate, ← ofAdd_nsmul]
    simp
  intro hfin
  rw [isOfFinOrder_iff_pow_eq_one] at hfin
  obtain ⟨m, hm, hmeq⟩ := hfin
  have h2 : (eps (sigmaProd n ^ n)) ^ m = 1 := by rw [← map_pow, hmeq, map_one]
  have h3 := center_finOrder_int (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, h2⟩)
  rw [map_pow, hsp, ← ofAdd_nsmul] at h3
  have hcon := congrArg Multiplicative.toAdd h3
  simp [nsmul_eq_mul] at hcon
  omega

#print axioms solution
