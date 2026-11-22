-- Prove2me | solution 1 for CircuitComplexity.DNF.flip_complexity_lb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:30.378147+00:00
-- url     : https://prove2.me/submissions/9ec29e37-fd74-49a2-b227-028a5eae55e0

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
public import Theorems.Thm_CircuitComplexity_DNF_term_mentions_all
public import Theorems.Thm_CircuitComplexity_full_term_unique
public import Theorems.Thm_CircuitComplexity_card_true_of_flip_sensitive
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity
namespace CircuitComplexity
namespace DNF
theorem _root_.solution (φ : DNF N) (hN : 1 ≤ N)
    (f : BitString N → Bool)
    (hcomp : ∀ x, φ.eval x = f x)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x) :
    2 ^ (N - 1) ≤ φ.complexity := by
  -- Every true assignment is covered by some term, and each full term covers ≤ 1 assignment
  suffices h : (Finset.univ.filter (fun x : BitString N => f x = true)).card ≤ φ.complexity by
    rwa [card_true_of_flip_sensitive hN f hflip] at h
  -- For each true x, find a term that x satisfies
  have hfind : ∀ x : BitString N, f x = true →
      ∃ term ∈ φ.terms, term.all (fun l => l.eval x) = true := by
    intro x hx
    have : φ.eval x = true := by rw [hcomp]; exact hx
    simpa [DNF.eval, List.any_eq_true] using this
  -- Each satisfiable term mentions all variables (so is satisfied by ≤ 1 assignment)
  have huniq : ∀ term ∈ φ.terms, ∀ x₁ x₂ : BitString N,
      term.all (fun l => l.eval x₁) = true →
      term.all (fun l => l.eval x₂) = true →
      x₁ = x₂ := by
    intro term hterm x₁ x₂ h₁ h₂
    have hfull := DNF.term_mentions_all φ f hcomp hflip term hterm x₁ h₁
    exact full_term_unique hfull h₁ h₂
  -- Count: |true-set| ≤ |terms| by injection via findIdx
  -- Reformulate as card ≤ card
  rw [show φ.complexity = (Finset.range φ.complexity).card from
    (Finset.card_range φ.complexity).symm]
  apply Finset.card_le_card_of_injOn
    (fun x => φ.terms.findIdx (fun t => t.all (fun l => l.eval x)))
  · -- MapsTo: findIdx lands in range
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, Set.mem_ofPred, true_and] at hx
    simp only [Finset.coe_range, Set.mem_Iio, DNF.complexity]
    simp_all
  · -- InjOn: two true assignments with same findIdx must be equal
    intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.coe_filter, Finset.mem_univ, Set.mem_ofPred, true_and] at hx₁ hx₂
    set k := φ.terms.findIdx (fun t => t.all (fun l => l.eval x₂))
    have hlt : k < φ.terms.length := by
      rw [List.findIdx_lt_length]; exact hfind x₂ hx₂
    have sat₂ : (φ.terms[k]'hlt).all (fun l => l.eval x₂) = true :=
      List.findIdx_getElem (w := hlt)
    have hlt₁ : φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁)) < φ.terms.length := by
      rw [List.findIdx_lt_length]; exact hfind x₁ hx₁
    have sat₁ : (φ.terms[φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁))]'hlt₁).all
        (fun l => l.eval x₁) = true :=
      List.findIdx_getElem (w := hlt₁)
    rw [show (φ.terms[φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁))]'hlt₁) =
        (φ.terms[k]'hlt) from by congr 1] at sat₁
    exact huniq _ (List.getElem_mem ..) x₁ x₂ sat₁ sat₂
end DNF
end CircuitComplexity
