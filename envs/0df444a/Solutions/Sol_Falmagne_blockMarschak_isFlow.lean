-- Prove2me | solution 1 for Falmagne.blockMarschak_isFlow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:53.320622+00:00
-- url     : https://prove2.me/submissions/ae8036d8-0fe7-48e9-b5d8-47badbadaa2c

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Conservation
public import Theorems.Thm_Falmagne_blockMarschak_source
public import Theorems.Thm_Falmagne_blockMarschak_conserve

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open Finset
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution [Nonempty X] (p : Finset X → X → ℝ)
    (hp : IsChoiceRule p)
    (hBM : ∀ x A, x ∈ A → 0 ≤ blockMarschak p x A) :
    IsFlow (blockMarschak p) 1 := by
  constructor
  · exact hBM
  · exact blockMarschak_source p hp
  · exact blockMarschak_conserve p hp
end Falmagne
