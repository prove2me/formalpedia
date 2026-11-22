-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.d_le_statePeriodModulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:55:46.481837+00:00
-- url     : https://prove2.me/submissions/f25a3a10-e6f9-408a-a546-d94b2df4a891

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (N d : ℕ) :
    d ≤ statePeriodModulus N d := Nat.le_mul_of_pos_right d (Nat.factorial_pos N)
end DeciSigma1.Holes.Periodic
