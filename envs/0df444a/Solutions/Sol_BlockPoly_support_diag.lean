-- Prove2me | solution 1 for BlockPoly.support_diag
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T15:10:01.623556+00:00
-- url     : https://prove2.me/submissions/4a25e1c9-d1ad-4f55-a661-73d2c595dd43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open BlockPoly
open MvPolynomial
variable {K σ : Type*} [Field K]
theorem BlockPoly_aux_diag_monomial {K σ : Type*} [Field K] (c : σ → K) (s : σ →₀ ℕ) (a : K) :
    BlockPoly.diag c (MvPolynomial.monomial s a) =
      MvPolynomial.monomial s (a * s.prod fun t e => c t ^ e) := by
  unfold BlockPoly.diag
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  simp only [mul_pow, Finsupp.prod_mul]
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_mul, mul_assoc]
  congr 1
  simp only [Finsupp.prod, map_prod, map_pow]

theorem BlockPoly_aux_coeff_diag {K σ : Type*} [Field K] (c : σ → K) (g : MvPolynomial σ K) (s : σ →₀ ℕ) :
    MvPolynomial.coeff s (BlockPoly.diag c g) = (s.prod fun t e => c t ^ e) * MvPolynomial.coeff s g := by
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [BlockPoly_aux_diag_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem BlockPoly.support_diag {c : σ → K} (hc : ∀ t, c t ≠ 0) (g : MvPolynomial σ K) :
    (diag c g).support = g.support := by
  ext s
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, BlockPoly_aux_coeff_diag]
  have hp : (s.prod fun t e => c t ^ e) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr (fun t _ => pow_ne_zero _ (hc t))
  exact ⟨fun h h2 => h (by rw [h2, mul_zero]), fun h => mul_ne_zero hp h⟩

theorem solution {c : σ → K} (hc : ∀ t, c t ≠ 0) (g : MvPolynomial σ K) :
    (diag c g).support = g.support := by
  ext s
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, BlockPoly_aux_coeff_diag]
  have hp : (s.prod fun t e => c t ^ e) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr (fun t _ => pow_ne_zero _ (hc t))
  exact ⟨fun h h2 => h (by rw [h2, mul_zero]), fun h => mul_ne_zero hp h⟩
