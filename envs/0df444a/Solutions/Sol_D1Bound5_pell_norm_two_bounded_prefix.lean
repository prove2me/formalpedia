-- Prove2me | solution 1 for D1Bound5.pell_norm_two_bounded_prefix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:20.403638+00:00
-- url     : https://prove2.me/submissions/d446a1f4-5003-4d6f-931b-22b7f36bb522

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellConvergentCompleteness_Definitions
import Theorems.Thm_D1Bound5_pellConvergentPair_div
import Theorems.Thm_D1Bound5_pellConvergentPair_pos
import Theorems.Thm_D1Bound5_pellConvergentPair_step_mono
import Theorems.Thm_D1Bound5_pell_norm_two_coprime
import Theorems.Thm_D1Bound5_pell_norm_two_is_convergent

section
namespace D1Bound5









theorem pellConvergentPair_coprime (x : ℝ) (n : ℕ) :
    IsCoprime (pellConvergentPair x n).1 (pellConvergentPair x n).2 := by
  induction n generalizing x with
  | zero =>
      change IsCoprime (⌊x⌋ : ℤ) 1
      exact ⟨0, 1, by ring⟩
  | succ n ih =>
      simpa only [pellConvergentPair, add_comm] using
        (ih (Int.fract x)⁻¹).symm.add_mul_right_left ⌊x⌋





theorem pellConvergentPair_num_mono {x : ℝ} (hx : Irrational x) (hx1 : 1 < x) :
    Monotone (fun n => (pellConvergentPair x n).1) :=
  monotone_nat_of_le_succ (fun n => (pellConvergentPair_step_mono hx hx1 n).1)





/-- A checked stopping numerator makes the finite prefix complete for every
positive norm-two solution with bounded numerator. No solution list is an
input hypothesis. -/
theorem _root_.solution {d x y X : ℤ} {N : ℕ}
    (hd : 7 ≤ d) (hns : ¬IsSquare d) (hx : 0 < x) (hy : 0 < y)
    (heq : x^2-d*y^2=2) (hX : x ≤ X)
    (hstop : X < (pellConvergentPair (Real.sqrt (d : ℝ)) N).1) :
    ∃ n < N, pellConvergentPair (Real.sqrt (d : ℝ)) n = (x,y) := by
  have hirr : Irrational (Real.sqrt (d : ℝ)) :=
    (irrational_sqrt_intCast_iff_of_nonneg (by omega)).mpr hns
  have hs1 : (1 : ℝ) < Real.sqrt (d : ℝ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d by exact_mod_cast (show 0 ≤ d by omega))
    have hs0 := Real.sqrt_nonneg (d : ℝ)
    have hd' : (7 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  obtain ⟨n,hn⟩ := pell_norm_two_is_convergent hd hx hy heq
  have hpair := pellConvergentPair_pos hirr hs1 n
  have hcop := pellConvergentPair_coprime (Real.sqrt (d : ℝ)) n
  have hxy := Rat.div_int_inj hy hpair.2
    (Int.isCoprime_iff_nat_coprime.mp (pell_norm_two_coprime hx heq))
    (Int.isCoprime_iff_nat_coprime.mp hcop)
    (hn.trans (pellConvergentPair_div hirr hs1 n).symm)
  have hlt : n < N := by
    by_contra hnN
    have hle : (pellConvergentPair (Real.sqrt (d : ℝ)) N).1 ≤
        (pellConvergentPair (Real.sqrt (d : ℝ)) n).1 :=
      pellConvergentPair_num_mono hirr hs1 (show N ≤ n by omega)
    rw [← hxy.1] at hle
    exact (not_lt_of_ge (hle.trans hX)) hstop
  exact ⟨n,hlt,Prod.ext hxy.1.symm hxy.2.symm⟩

end D1Bound5
end
