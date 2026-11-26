-- Prove2me | solution 1 for Falmagne.blockMarschak_conserve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:04.861846+00:00
-- url     : https://prove2.me/submissions/695ec52f-3931-4a52-b974-eea082181918

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Conservation
public import Theorems.Thm_Falmagne_blockMarschak_not_mem
public import Theorems.Thm_Falmagne_blockMarschak_total

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open Finset
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution (p : Finset X → X → ℝ) (hp : IsChoiceRule p)
    (A : Finset X) (hA : A.Nonempty) (hproper : A ≠ univ) :
    (∑ x ∈ A, blockMarschak p x A) =
      ∑ x ∈ univ \ A, blockMarschak p x (insert x A) := by
  have htotal := blockMarschak_total p hp A hA
  rw [if_neg hproper] at htotal
  have hoff : (∑ x ∈ univ \ A, blockMarschak p x A) =
      -(∑ x ∈ univ \ A, blockMarschak p x (insert x A)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro x hx
    exact blockMarschak_not_mem p hp A x (mem_sdiff.mp hx).2
  have hsplit := sum_sdiff (subset_univ A) (f := fun x => blockMarschak p x A)
  rw [hoff, htotal] at hsplit
  linarith
end Falmagne
