-- Prove2me | solution 1 for FourierJacobi.Algebra.fifty_region_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:01.321509+00:00
-- url     : https://prove2.me/submissions/80d272d3-ccb5-41d7-b813-18d1fb796c76

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Theorems.Thm_FourierJacobi_Algebra_region_term_cleared
import Theorems.Thm_FourierJacobi_Algebra_region_numerators_sum

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace FourierJacobi.Algebra
theorem _root_.solution (t d U V : K) (hd : d ≠ 0)
    (hP : 1 - d * V * t ≠ 0) (hN : 1 - V * t / d ≠ 0)
    (hE : 1 - V ^ 2 * t ^ 2 ≠ 0) (hF : 1 - U * t ^ 2 ≠ 0)
    (hG : 1 - U * t ^ 4 ≠ 0) :
    (∑ i : Fin 50, regionTerms t d U V i) = regionKernel t d U V := by
  let P := 1 - d * V * t
  let N := 1 - V * t / d
  let E := 1 - V ^ 2 * t ^ 2
  let F := 1 - U * t ^ 2
  let G := 1 - U * t ^ 4
  have hh := region_numerators_sum t d U V hd
  have hs : (d ^ 2 * P * N * E * F * G) *
      (∑ i : Fin 50, regionTerms t d U V i) =
      E * F * G * kernelNumerator t d U V := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ i : Fin 50, rawRegionNumerators t d U V P N E F G i := by
        apply Finset.sum_congr rfl
        intro i _
        exact region_term_cleared t d U V P N E F G hd hP hN hE hF hG i
      _ = _ := hh
  have hden : d ^ 2 * P * N * E * F * G ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 2 hd) hP) hN) hE) hF) hG
  apply (mul_right_inj' hden).mp
  rw [hs]
  change E * F * G * kernelNumerator t d U V =
    (d ^ 2 * P * N * E * F * G) * (kernelNumerator t d U V / (d ^ 2 * P * N))
  have hpn : d ^ 2 * P * N ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hd) hP) hN
  have hcancel (x y z : K) (hy : y ≠ 0) : y * z * (x / y) = z * x := by
    field_simp <;> ring
  simpa [mul_assoc] using
    (hcancel (kernelNumerator t d U V) (d ^ 2 * P * N) (E * F * G) hpn).symm
end FourierJacobi.Algebra
