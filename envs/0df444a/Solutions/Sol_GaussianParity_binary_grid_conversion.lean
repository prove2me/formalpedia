-- Prove2me | solution 1 for GaussianParity.binary_grid_conversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.497676+00:00
-- url     : https://prove2.me/submissions/c8ee7646-bf5a-4930-be0c-7a5ac0bcaf8d

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Theorems.Thm_GaussianParity_even_binary_conversion
import Theorems.Thm_GaussianParity_odd_binary_conversion

set_option autoImplicit true
open GaussianParity
namespace GaussianParity
theorem _root_.solution (D : Nat) (z : GInt) :
    ∃ w : GInt, repeatPi D w = scale ((2 : Int)^((D+1)/2)) z := by
  have hp : D % 2 = 0 ∨ D % 2 = 1 := by omega
  rcases hp with he | ho
  · have hd : D = 2*(D/2) := by omega
    have hceil : (D+1)/2 = D/2 := by omega
    refine ⟨repeatNegI (D/2) z, ?_⟩
    calc
      repeatPi D (repeatNegI (D/2) z) =
          repeatPi (2*(D/2)) (repeatNegI (D/2) z) :=
            congrArg (fun n => repeatPi n (repeatNegI (D/2) z)) hd
      _ = scale ((2 : Int)^(D/2)) z := even_binary_conversion (D/2) z
      _ = scale ((2 : Int)^((D+1)/2)) z := by rw [hceil]
  · have hd : D = 2*(D/2)+1 := by omega
    have hceil : (D+1)/2 = D/2+1 := by omega
    refine ⟨repeatNegI (D/2+1) (mulPi z), ?_⟩
    calc
      repeatPi D (repeatNegI (D/2+1) (mulPi z)) =
          repeatPi (2*(D/2)+1) (repeatNegI (D/2+1) (mulPi z)) :=
            congrArg (fun n => repeatPi n (repeatNegI (D/2+1) (mulPi z))) hd
      _ = scale ((2 : Int)^(D/2+1)) z := odd_binary_conversion (D/2) z
      _ = scale ((2 : Int)^((D+1)/2)) z := by rw [hceil]
end GaussianParity
