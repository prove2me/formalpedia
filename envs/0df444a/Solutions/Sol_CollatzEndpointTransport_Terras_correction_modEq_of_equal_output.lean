-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.correction_modEq_of_equal_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:50.777948+00:00
-- url     : https://prove2.me/submissions/43a1f76f-6aaa-4c5e-804c-baffaf49a21a

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
import Theorems.Thm_CollatzEndpointTransport_Terras_pow_two_mul_iterate_eq_affine
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {M s n₁ n₂ : ℕ}
    (hs₁ : oddCount M n₁ = s)
    (hs₂ : oddCount M n₂ = s)
    (hout : (T^[M]) n₁ = (T^[M]) n₂) :
    Nat.ModEq (3 ^ s)
      (integerCorrection M n₁) (integerCorrection M n₂) := by
  have h₁ :
      2 ^ M * (T^[M]) n₁ =
        3 ^ s * n₁ + integerCorrection M n₁ := by
    simpa [hs₁] using pow_two_mul_iterate_eq_affine M n₁
  have h₂ :
      2 ^ M * (T^[M]) n₂ =
        3 ^ s * n₂ + integerCorrection M n₂ := by
    simpa [hs₂] using pow_two_mul_iterate_eq_affine M n₂
  have hEq :
      3 ^ s * n₁ + integerCorrection M n₁ =
        3 ^ s * n₂ + integerCorrection M n₂ := by
    calc
      3 ^ s * n₁ + integerCorrection M n₁ =
          2 ^ M * (T^[M]) n₁ := h₁.symm
      _ = 2 ^ M * (T^[M]) n₂ := by rw [hout]
      _ = 3 ^ s * n₂ + integerCorrection M n₂ := h₂
  rw [Nat.ModEq]
  have hmod := congrArg (fun x : ℕ => x % 3 ^ s) hEq
  simpa [Nat.add_mod, Nat.mul_mod] using hmod
end CollatzEndpointTransport.Terras
