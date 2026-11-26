-- Prove2me | solution 1 for Falmagne.blockMarschak_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:16.090669+00:00
-- url     : https://prove2.me/submissions/072ad269-5d16-453b-88ca-f2e29264eba7

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Conservation
public import Theorems.Thm_Falmagne_blockMarschak_univ

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open Finset
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution [Nonempty X] (p : Finset X → X → ℝ)
    (hp : IsChoiceRule p) : ∑ x : X, blockMarschak p x univ = 1 := by
  simp_rw [blockMarschak_univ]
  exact hp.2.2 univ univ_nonempty
end Falmagne
