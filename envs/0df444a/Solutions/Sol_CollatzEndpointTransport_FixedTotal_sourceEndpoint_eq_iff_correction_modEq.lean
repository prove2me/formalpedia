-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpoint_eq_iff_correction_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:33.723832+00:00
-- url     : https://prove2.me/submissions/f333c5b3-56c0-4600-bcfb-e682f86efb6f

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_eq_three_pow_add_residueEndpoint
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceResidueEndpoint_lt_three_pow
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_collision_modEq_correction
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceResidueEndpoint_mul_modEq_correction

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} {x y : SourceCode M}
    (hsx : sourceCodeOddCount x = s)
    (hsy : sourceCodeOddCount y = s) :
    sourceEndpoint x = sourceEndpoint y ↔
      Nat.ModEq (3 ^ s) (sourceCodeCorrection x)
        (sourceCodeCorrection y) := by
  constructor
  · exact sourceEndpoint_collision_modEq_correction hsx hsy
  · intro hcorr
    have hx := sourceResidueEndpoint_mul_modEq_correction hsx
    have hy := sourceResidueEndpoint_mul_modEq_correction hsy
    have hmul :
        Nat.ModEq (3 ^ s)
          (2 ^ M * sourceResidueEndpoint x)
          (2 ^ M * sourceResidueEndpoint y) :=
      hx.trans (hcorr.trans hy.symm)
    have hcop : Nat.gcd (3 ^ s) (2 ^ M) = 1 :=
      (Nat.Coprime.pow s M
        (by norm_num : Nat.Coprime 3 2)).gcd_eq_one
    have hresMod :
        Nat.ModEq (3 ^ s)
          (sourceResidueEndpoint x) (sourceResidueEndpoint y) :=
      Nat.ModEq.cancel_left_of_coprime hcop hmul
    have hxlt := sourceResidueEndpoint_lt_three_pow (x := x) hsx
    have hylt := sourceResidueEndpoint_lt_three_pow (x := y) hsy
    rw [Nat.ModEq, Nat.mod_eq_of_lt hxlt,
      Nat.mod_eq_of_lt hylt] at hresMod
    rw [sourceEndpoint_eq_three_pow_add_residueEndpoint,
      sourceEndpoint_eq_three_pow_add_residueEndpoint, hsx, hsy, hresMod]
end CollatzEndpointTransport.FixedTotal
