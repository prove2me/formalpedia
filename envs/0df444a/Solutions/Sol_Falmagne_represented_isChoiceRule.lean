-- Prove2me | solution 1 for Falmagne.represented_isChoiceRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:42.71007+00:00
-- url     : https://prove2.me/submissions/2d9abfd4-2f90-4964-836b-99001ef7e13c

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Representation
public import Theorems.Thm_Falmagne_rankingEdge_eq_zero_of_not_mem
public import Theorems.Thm_Falmagne_mem_lowerContour
public import Theorems.Thm_Falmagne_rankingChoice_nonneg
public import Theorems.Thm_Falmagne_sum_rankingChoice
attribute [local simp] Falmagne.mem_lowerContour


attribute [local simp] Falmagne.rankingEdge_eq_zero_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
namespace Falmagne
theorem _root_.solution {w : RankingLaw X} {p : Finset X → X → ℝ}
    (hw : IsRankingLaw w) (hp : Represents w p) : IsChoiceRule p := by
  unfold Represents at hp
  refine ⟨?_, ?_, ?_⟩
  · intro A x
    rw [hp A x]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hw.1 l) (rankingChoice_nonneg l A x)
  · intro A x hx
    rw [hp A x]
    simp [rankingChoice, hx]
  · intro A hA
    simp_rw [hp]
    unfold Finsupp.sum
    rw [Finset.sum_comm]
    calc
      _ = ∑ l ∈ w.support, w l * (∑ x ∈ A, rankingChoice l A x) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum]
      _ = ∑ l ∈ w.support, w l := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [sum_rankingChoice (hw.2.1 l hl) hA, mul_one]
      _ = 1 := hw.2.2
end Falmagne
