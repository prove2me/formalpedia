-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.d_le_boundaryMargin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:24.163931+00:00
-- url     : https://prove2.me/submissions/46358277-a858-4cd0-a135-877f293cada1

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Periodic_d_le_statePeriodModulus

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (N d : ℕ) : d ≤ boundaryMargin N d := by
  have := d_le_statePeriodModulus N d; unfold boundaryMargin stateTransientLength; omega
end DeciSigma1.Holes.Periodic
