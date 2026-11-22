-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.sat_raySys_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:51:43.183998+00:00
-- url     : https://prove2.me/submissions/05867d74-2e8d-4641-b5a4-62d4c1f74792

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_sat_ofFinset_iff
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata
variable {ι : Type}
variable [DecidableEq α] [Fintype S] (M : StructuralReader α S k) [Fintype ι] [DecidableEq ι]
variable {M}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {st : ι → S} {Ω : ι → Ray α} {J : ι → ℕ} {x : ι → ℤ} :
    (raySystem M st Ω J).Sat x ↔ ∀ i j, i ≠ j → ∀ a < rayHorizon S (Ω i), ∀ b ≤ J j,
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st j) (Ω j) b) = true →
      (∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t)) → x i + ((b : ℤ) - a + 1) ≤ x j := by
  rw [raySystem, DifferenceSystem.sat_ofFinset_iff]
  constructor
  · intro h i j hij a ha b hb hadm heq
    apply h (i, j, (b : ℤ) - a + 1)
    simp only [rayEdges, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨i, j, ?_⟩
    rw [if_neg hij, Finset.mem_image]
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr (by omega)⟩, hadm, heq⟩, rfl⟩
  · intro h e he
    simp only [rayEdges, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
    obtain ⟨i, j, he⟩ := he
    split_ifs at he with hij
    · simp at he
    · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hab, hadm, heq⟩ := Finset.mem_filter.mp hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact h i j hij a (Finset.mem_range.mp ha) b (by have := Finset.mem_range.mp hb; omega)
        hadm heq
end DeciSigma1.Holes.Tail
