-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.sub_lt_pow_two_of_equal_iterate_same_oddCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:08.066095+00:00
-- url     : https://prove2.me/submissions/450bea69-cf13-4cf4-a2ab-91703c0dd0a0

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
import Theorems.Thm_CollatzEndpointTransport_Terras_pow_two_mul_iterate_eq_affine
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_lt_scale
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {d k n m : ℕ}
    (hnm : n < m)
    (hnk : oddCount d n = k)
    (hmk : oddCount d m = k)
    (hout : (T^[d]) n = (T^[d]) m) :
    m - n < 2 ^ d := by
  have hnAffine := pow_two_mul_iterate_eq_affine d n
  have hmAffine := pow_two_mul_iterate_eq_affine d m
  rw [hnk] at hnAffine
  rw [hmk] at hmAffine
  have hEq :
      3 ^ k * n + integerCorrection d n =
        3 ^ k * m + integerCorrection d m := by
    calc
      3 ^ k * n + integerCorrection d n =
          2 ^ d * (T^[d]) n := hnAffine.symm
      _ = 2 ^ d * (T^[d]) m := by rw [hout]
      _ = 3 ^ k * m + integerCorrection d m := hmAffine
  have hmdecomp : m = n + (m - n) := by omega
  have hEq' :
      3 ^ k * n + integerCorrection d n =
        3 ^ k * n +
          (3 ^ k * (m - n) + integerCorrection d m) := by
    rw [hEq, hmdecomp]
    simp only [Nat.add_sub_cancel_left]
    ring
  have hrest :
      integerCorrection d n =
        3 ^ k * (m - n) + integerCorrection d m :=
    Nat.add_left_cancel hEq'
  have hle : 3 ^ k * (m - n) ≤ integerCorrection d n := by
    omega
  have hcorr : integerCorrection d n < 3 ^ k * 2 ^ d := by
    simpa [hnk] using integerCorrection_lt_scale d n
  have hmul : 3 ^ k * (m - n) < 3 ^ k * 2 ^ d :=
    lt_of_le_of_lt hle hcorr
  exact (Nat.mul_lt_mul_left (pow_pos (by norm_num) k)).mp hmul
end CollatzEndpointTransport.Terras
