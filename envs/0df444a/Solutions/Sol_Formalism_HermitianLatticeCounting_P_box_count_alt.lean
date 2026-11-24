-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.box_count_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:16.283707+00:00
-- url     : https://prove2.me/submissions/cc1c2a8d-137f-4a69-8529-6087fc755272

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_card_separated_set_le_prod
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_finite_of_finset_card_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : BoxCount := by
  intro ι _ s Λ ν B hν hB hΛ
  apply finite_of_finset_card_bound
  intro S hS
  set Q := (∏ v, B v ^ 2) / ν with hQ
  set M := max 1 Q with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have hPB : 0 < ∏ v, B v ^ 2 := Finset.prod_pos fun v _ => pow_pos (hB v) 2
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h1 : S.card ≤ 1 := Finset.card_le_one.mpr fun a _ b _ => Subsingleton.elim a b
    have h2 : (1:ℝ) ≤ 9 ^ (s * Fintype.card ι) * M ^ s :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hM1)
    have h3 : (S.card : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith
  · set f := Fintype.card ι with hf
    have hf0 : 0 < f := Fintype.card_pos
    have hfR : (0:ℝ) < f := by exact_mod_cast hf0
    set τ := M ^ (1 / (2 * (f:ℝ))) with hτ
    have hτ1 : 1 ≤ τ := Real.one_le_rpow hM1 (by positivity)
    have hτ0 : 0 < τ := by linarith
    have hτpow : τ ^ (2 * f) = M := by
      rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le]
      have : 1 / (2 * (f:ℝ)) * ((2 * f : ℕ) : ℝ) = 1 := by push_cast; field_simp
      rw [this, Real.rpow_one]
    have hprod : ∏ v, (2 * (B v / (2 * τ))) ^ 2 ≤ ν := by
      have e : ∀ v, (2 * (B v / (2 * τ))) ^ 2 = B v ^ 2 / τ ^ 2 := fun v => by field_simp
      simp only [e]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, ← hf, hτpow,
        div_le_iff₀ hM0]
      have : Q ≤ M := le_max_right _ _
      rw [hQ, div_le_iff₀ hν] at this
      linarith
    have := card_separated_set_le_prod S (fun v => B v / (2 * τ)) B (fun v => by have := hB v; positivity)
      (fun v => (hB v).le) (fun c hc => (hS hc).2) (by
        intro c hc d hd hcd
        by_contra hcon
        push_neg at hcon
        have hne : c - d ≠ 0 := sub_ne_zero.mpr hcd
        have h1 := hΛ (c - d) (Λ.sub_mem (hS hc).1 (hS hd).1) hne
        have hpos : ∀ v ∈ Finset.univ, 0 < ‖(c - d) v‖ ^ 2 := by
          intro v _
          by_contra h0
          have hz : ‖(c - d) v‖ ^ 2 = 0 := le_antisymm (not_lt.mp h0) (by positivity)
          have : ∏ v, ‖(c - d) v‖ ^ 2 = 0 := Finset.prod_eq_zero (Finset.mem_univ v) hz
          linarith
        have h2 : ∏ v, ‖(c - d) v‖ ^ 2 < ∏ v, (2 * (B v / (2 * τ))) ^ 2 :=
          Finset.prod_lt_prod_of_nonempty hpos (fun v _ =>
            pow_lt_pow_left₀ (hcon v) (norm_nonneg _) (by norm_num)) Finset.univ_nonempty
        linarith)
    refine this.trans ?_
    have hdim : finrank ℝ (EuclideanSpace ℂ (Fin s)) = 2 * s := by
      rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin s)), Complex.finrank_real_complex,
        finrank_euclideanSpace, Fintype.card_fin]
    rw [hdim]
    calc ∏ v, ((B v + B v / (2 * τ)) / (B v / (2 * τ))) ^ (2 * s) ≤ ∏ _v : ι, (3 * τ) ^ (2 * s) := by
          refine Finset.prod_le_prod (fun v _ => by have := hB v; positivity) fun v _ => ?_
          have hb := hB v
          have e : (B v + B v / (2 * τ)) / (B v / (2 * τ)) = 2 * τ + 1 := by field_simp
          rw [e]
          exact pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 9 ^ (s * f) * (τ ^ (2 * f)) ^ s := by
          rw [Finset.prod_const, Finset.card_univ, ← hf, ← pow_mul, mul_pow, ← pow_mul,
            show (9:ℝ) = 3 ^ 2 by norm_num, ← pow_mul]
          congr 2 <;> ring
      _ = _ := by rw [hτpow]
end Formalism.HermitianLatticeCounting.P
