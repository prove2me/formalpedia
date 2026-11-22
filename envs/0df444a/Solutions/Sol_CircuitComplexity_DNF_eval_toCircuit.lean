-- Prove2me | solution 1 for CircuitComplexity.DNF.eval_toCircuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:18.265839+00:00
-- url     : https://prove2.me/submissions/c2dab751-83e2-4966-8f12-fb5cccf55272

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_ge
public import Theorems.Thm_CircuitComplexity_Circuit_wireValue_lt
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


section
@[expose] public section
set_option autoImplicit true
set_option autoImplicit true
namespace CircuitComplexity
private lemma xor_neg_polarity_eq_eval (l : Literal N) (x : BitString N) :
    (!l.polarity).xor (x l.var) = l.eval x := by
  simp only [Literal.eval]
  cases l.polarity <;> simp
private lemma foldl_bor_eq_true (n : Nat) (g : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc || g i) false = true) ↔ (∃ i : Fin n, g i = true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    constructor
    · intro h
      rw [Bool.or_eq_true] at h
      cases h with
      | inl h => rw [ih] at h; obtain ⟨j, hj⟩ := h; exact ⟨j.castSucc, hj⟩
      | inr h => exact ⟨Fin.last n, h⟩
    · intro ⟨i, hi⟩
      rw [Bool.or_eq_true]
      rcases Fin.lastCases (motive := fun i => (∃ j : Fin n, i = j.castSucc) ∨ i = Fin.last n)
        (Or.inr rfl) (fun j => Or.inl ⟨j, rfl⟩) i with ⟨j, rfl⟩ | rfl
      · left; rw [ih]; exact ⟨j, hi⟩
      · right; exact hi
private lemma foldl_band_eq_true (n : Nat) (g : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc && g i) true = true) ↔ (∀ i : Fin n, g i = true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last, Bool.and_eq_true]
    refine ⟨fun ⟨h1, h2⟩ i => Fin.lastCases h2 (fun j => (ih _).mp h1 j) i, fun h => ?_⟩
    exact ⟨(ih _).mpr (fun j => h j.castSucc), h (Fin.last n)⟩
private lemma foldl_bor_eq_list_any {α : Type} (l : List α) (p : α → Bool) :
    Fin.foldl l.length (fun acc (i : Fin l.length) => acc || p (l.get i)) false = l.any p := by
  have h_iff : (Fin.foldl l.length (fun acc i => acc || p (l.get i)) false = true) ↔
      (l.any p = true) := by
    rw [foldl_bor_eq_true, List.any_eq_true]
    refine ⟨fun ⟨i, hi⟩ => ⟨l.get i, List.get_mem l i, hi⟩, fun ⟨a, ha, hp⟩ => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨i, hp⟩
  cases h1 : Fin.foldl l.length (fun acc i => acc || p (l.get i)) false <;>
    cases h2 : l.any p <;> simp_all
private lemma foldl_band_eq_list_all {α : Type} (l : List α) (p : α → Bool) :
    Fin.foldl l.length (fun acc (i : Fin l.length) => acc && p (l.get i)) true = l.all p := by
  have h_iff : (Fin.foldl l.length (fun acc i => acc && p (l.get i)) true = true) ↔
      (l.all p = true) := by
    rw [foldl_band_eq_true, List.all_eq_true]
    refine ⟨fun h a ha => ?_, fun h i => h (l.get i) (List.get_mem l i)⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact h i
  cases h1 : Fin.foldl l.length (fun acc i => acc && p (l.get i)) true <;>
    cases h2 : l.all p <;> simp_all
namespace CNF
private lemma wireValue_gate [NeZero N] (φ : CNF N) (x : BitString N) (i : Fin φ.complexity) :
    φ.toCircuit.wireValue x ⟨N + i.val, by omega⟩ =
      (φ.clauses.get ⟨i.val, i.isLt⟩).any (fun l => l.eval x) := by
  have hge : ¬ ((⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val < N) := by simp
  rw [Circuit.wireValue_ge _ x _ hge]
  -- Normalize gate index
  have hgi : φ.toCircuit.gates ⟨(⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val - N,
    (by omega)⟩ = φ.toCircuit.gates i := by congr 1; ext; simp
  rw [hgi]
  -- Unfold gate definition
  simp only [toCircuit, Gate.eval, Basis.unboundedAON, AONOp.eval]
  -- Handle wireValue for primary inputs + xor-negation inside foldl
  conv_lhs => arg 2; ext acc j; arg 2
              rw [Circuit.wireValue_lt _ _ _
                ((φ.clauses.get ⟨↑i, i.isLt⟩).get j).var.isLt, xor_neg_polarity_eq_eval]
  exact foldl_bor_eq_list_any (φ.clauses.get ⟨↑i, i.isLt⟩) (fun l => l.eval x)
end CNF
namespace DNF
private lemma wireValue_gate [NeZero N] (φ : DNF N) (x : BitString N) (i : Fin φ.complexity) :
    φ.toCircuit.wireValue x ⟨N + i.val, by omega⟩ =
      (φ.terms.get ⟨i.val, i.isLt⟩).all (fun l => l.eval x) := by
  have hge : ¬ ((⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val < N) := by simp
  rw [Circuit.wireValue_ge _ x _ hge]
  -- Normalize gate index
  have hgi : φ.toCircuit.gates ⟨(⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val - N,
    (by omega)⟩ = φ.toCircuit.gates i := by congr 1; ext; simp
  rw [hgi]
  -- Unfold gate definition
  simp only [toCircuit, Gate.eval, Basis.unboundedAON, AONOp.eval]
  -- Handle wireValue for primary inputs + xor-negation inside foldl
  conv_lhs => arg 2; ext acc j; arg 2
              rw [Circuit.wireValue_lt _ _ _
                ((φ.terms.get ⟨↑i, i.isLt⟩).get j).var.isLt, xor_neg_polarity_eq_eval]
  exact foldl_band_eq_list_all (φ.terms.get ⟨↑i, i.isLt⟩) (fun l => l.eval x)
end DNF
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity
open CircuitComplexity.DNF
namespace CircuitComplexity.DNF
theorem _root_.solution [NeZero N] (φ : DNF N) :
    (fun x => (φ.toCircuit.eval x) 0) = φ.eval := by
  funext x
  simp only [Circuit.eval, eval, toCircuit, Gate.eval, Basis.unboundedAON, Bool.false_xor,
    AONOp.eval]
  -- Convert struct-literal wireValue back to φ.toCircuit form for wireValue_gate
  change Fin.foldl φ.complexity
    (fun acc j => acc || φ.toCircuit.wireValue x ⟨N + j.val, by omega⟩) false =
    φ.terms.any (fun term => term.all fun l => l.eval x)
  conv_lhs => arg 2; ext acc j; arg 2; rw [wireValue_gate φ x j]
  exact foldl_bor_eq_list_any φ.terms (fun term => term.all fun l => l.eval x)
end CircuitComplexity.DNF
