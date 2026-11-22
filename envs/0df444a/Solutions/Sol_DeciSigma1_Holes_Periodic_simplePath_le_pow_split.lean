-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.simplePath_le_pow_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:14.095548+00:00
-- url     : https://prove2.me/submissions/2525db19-9864-48fe-862a-5d311701a58a

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_simplePath_le_pow_prefix
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Arithmetic DeciSigma1.Words
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
variable {N : ℕ} {z : {P // P ∈ piecesOf W ρ} → ℤ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {β γ : Type*} (f : β → List γ) (head : β → Prop)
    [DecidablePred head] (h : ℕ) (p : List β) (hnd : p.Nodup)
    (hp : p.IsChain (fun x y => f x <+: f y ∨ f y <+: f x))
    (hh : ∀ c : Finset β, (∀ x ∈ c, x ∈ p) → (∀ x ∈ c, head x) →
      (∀ x ∈ c, ∀ y ∈ c, f x <+: f y ∨ f y <+: f x) → c.card ≤ h) :
    p.length + 1 ≤ ((p.filter (fun x => decide (¬ head x))).length + 1) * 2 ^ h := by
  classical
  generalize he : p.length = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hall : ∀ x ∈ p, head x
    · have hb := simplePath_le_pow_prefix f h p hnd hp
        (fun c hc hcomp => hh c hc (fun x hx => hall x (hc x hx)) hcomp)
      have hempty : p.filter (fun x => decide (¬ head x)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simp [hall x hx]
      rw [hempty]
      simp only [List.length_nil, zero_add, one_mul]
      have : 1 ≤ 2 ^ h := Nat.one_le_two_pow
      omega
    · obtain ⟨m, hm⟩ := not_forall.mp hall
      obtain ⟨hm, hmtail⟩ := _root_.not_imp.mp hm
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hm
      have hnd' := List.nodup_middle.mp hnd
      rw [List.nodup_cons] at hnd'
      have hs_nd := (List.nodup_append.mp hnd'.2).1
      have ht_nd := (List.nodup_append.mp hnd'.2).2.1
      have hsplit := List.isChain_split.mp hp
      have hs_ch := (List.isChain_append.mp hsplit.1).1
      have ht_ch := hsplit.2.tail
      have hside : ∀ q : List β, (∀ x ∈ q, x ∈ s ++ m :: t) → q.length < n →
          q.Nodup → q.IsChain (fun x y => f x <+: f y ∨ f y <+: f x) →
          q.length + 1 ≤ ((q.filter (fun x => decide (¬ head x))).length + 1) * 2 ^ h := by
        intro q hq hqn hqnd hqch
        exact ih q.length hqn q hqnd hqch
          (fun c hc => hh c (fun x hx => hq x (hc x hx))) rfl
      have hs := hside s (fun x hx => List.mem_append_left _ hx)
        (by simp only [List.length_append, List.length_cons] at he; omega) hs_nd hs_ch
      have ht := hside t (fun x hx => List.mem_append_right _ (List.mem_cons_of_mem _ hx))
        (by simp only [List.length_append, List.length_cons] at he; omega) ht_nd ht_ch
      simp only [List.length_append, List.length_cons] at he
      simp [List.filter_append, hmtail] at hs ht ⊢
      nlinarith
end DeciSigma1.Holes.Periodic
