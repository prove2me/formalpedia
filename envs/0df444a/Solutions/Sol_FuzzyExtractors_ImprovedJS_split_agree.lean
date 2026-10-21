-- Prove2me | solution 1 for FuzzyExtractors.ImprovedJS.split_agree
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-20T08:40:37.870149+00:00
-- url     : https://prove2.me/submissions/d725f30f-a8a1-400f-b4ba-501ff993f22b

import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

open Polynomial
open FuzzyExtractors.ImprovedJS

theorem solution {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s)
    (w : Finset 𝔽) (hw : w.card = s) :
    ∃ q : 𝔽[X], charPoly w = pHigh s t (sketchCoeffs s t w) + q ∧
      q.degree < ((s - t : ℕ) : WithBot ℕ) ∧
      ∀ x ∈ w, (pHigh s t (sketchCoeffs s t w)).eval x = -(q.eval x) := by
  classical
  let p := charPoly w
  let H := pHigh s t (sketchCoeffs s t w)
  have hpdeg : p.natDegree = s := by
    simpa [p, charPoly] using (natDegree_finsetProd_X_sub_C_eq_card w (fun x : 𝔽 => x)).trans hw
  have hpmonic : p.Monic := by
    exact monic_prod_X_sub_C (fun x : 𝔽 => x) w
  have hindex : ∀ i : Fin t, s - 1 - (i : ℕ) < s := by
    intro i
    have hi := i.isLt
    omega
  have hHcoeff : ∀ n, s - t ≤ n → H.coeff n = p.coeff n := by
    intro n hn
    by_cases hns : n < s
    · let j : Fin t := ⟨s - 1 - n, by omega⟩
      have hj : s - 1 - (j : ℕ) = n := by dsimp [j]; omega
      have hsum : (∑ i : Fin t, C (p.coeff (s - 1 - (i : ℕ))) * X ^ (s - 1 - (i : ℕ))).coeff n = p.coeff n := by
        rw [finsetSum_coeff, Finset.sum_eq_single j]
        · simp [coeff_C_mul_X_pow, hj]
        · intro i _ hij
          rw [coeff_C_mul_X_pow, if_neg]
          intro he
          apply hij
          apply Fin.ext
          have hi := i.isLt
          dsimp [j] at *
          omega
        · simp
      dsimp [H, pHigh, sketchCoeffs]
      rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add]
      exact hsum
    · have hsum : (∑ i : Fin t, C (p.coeff (s - 1 - (i : ℕ))) * X ^ (s - 1 - (i : ℕ))).coeff n = 0 := by
        rw [finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro i _
        rw [coeff_C_mul_X_pow, if_neg (by have hi := hindex i; omega)]
      dsimp [H, pHigh, sketchCoeffs]
      rw [coeff_add, hsum, add_zero, coeff_X_pow]
      by_cases heq : n = s
      · rw [if_pos heq, heq]
        simpa [hpdeg] using hpmonic.coeff_natDegree.symm
      · rw [if_neg heq]
        symm
        exact coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨p - H, ?_, ?_, ?_⟩
  · dsimp [p, H]
    ring
  · rw [degree_lt_iff_coeff_zero]
    intro n hn
    rw [coeff_sub, hHcoeff n hn, sub_self]
  · intro x hx
    have hxzero : p.eval x = 0 := by
      dsimp [p, charPoly]
      rw [eval_prod]
      apply Finset.prod_eq_zero hx
      simp
    change H.eval x = -((p - H).eval x)
    rw [eval_sub, hxzero]
    ring

#print axioms solution
