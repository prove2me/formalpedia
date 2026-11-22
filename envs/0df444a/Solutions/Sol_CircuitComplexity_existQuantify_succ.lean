-- Prove2me | solution 1 for CircuitComplexity.existQuantify_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:48.207161+00:00
-- url     : https://prove2.me/submissions/81185641-6827-4368-87ff-fae5086c1bc4

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
public import Theorems.Thm_CircuitComplexity_existQuantify_eq_true
public import Theorems.Thm_CircuitComplexity_forallQuantify_eq_true
public import Theorems.Thm_CircuitComplexity_existQuantify_const_true
public import Theorems.Thm_CircuitComplexity_existQuantify_const_false
public import Theorems.Thm_CircuitComplexity_forallQuantify_const_true
public import Theorems.Thm_CircuitComplexity_forallQuantify_const_false
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth


attribute [local simp] CircuitComplexity.existQuantify_eq_true
attribute [local simp] CircuitComplexity.forallQuantify_eq_true
attribute [local simp] CircuitComplexity.existQuantify_const_true
attribute [local simp] CircuitComplexity.existQuantify_const_false
attribute [local simp] CircuitComplexity.forallQuantify_const_true
attribute [local simp] CircuitComplexity.forallQuantify_const_false

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}
namespace CircuitComplexity
theorem _root_.solution (f : BitString ((k + 1) + m) → Bool) (y : BitString m) :
    existQuantify (k := k + 1) f y =
    ((existQuantify (k := k) (restrictFirst f false) y) ||
     (existQuantify (k := k) (restrictFirst f true) y)) := by
  have bool_eq : ∀ (a b : Bool), a = b ↔ (a = true ↔ b = true) := by decide
  rw [bool_eq]
  simp only [existQuantify_eq_true, Bool.or_eq_true, restrictFirst]
  constructor
  · rintro ⟨a, ha⟩
    by_cases hb : a ⟨0, by omega⟩ = true
    · right
      refine ⟨fun i => a ⟨i.val + 1, by omega⟩, ?_⟩
      convert ha using 2
      ext ⟨i, hi⟩
      simp only [Fin.append, Fin.addCases]
      split_ifs with h1 h2 h3 <;> simp_all <;> try omega
      · simp_all [Fin.castLT]
      · congr 1
        simp [Fin.ext_iff]
        omega
      · congr 1
        simp [Fin.ext_iff]
        omega
    · left
      refine ⟨fun i => a ⟨i.val + 1, by omega⟩, ?_⟩
      convert ha using 2
      ext ⟨i, hi⟩
      simp only [Fin.append, Fin.addCases]
      split_ifs with h1 h2 h3 <;> simp_all <;> try omega
      · simp_all [Fin.castLT]
      · congr 1
        simp [Fin.ext_iff]
        omega
      · congr 1
        simp [Fin.ext_iff]
        omega
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · refine ⟨fun i => if h : i.val = 0 then false else x ⟨i.val - 1, by omega⟩, ?_⟩
      convert hx using 2
      ext ⟨i, hi⟩
      simp only [Fin.append, Fin.addCases]
      split_ifs <;> simp_all <;> try omega
      · exfalso
        simp_all [Fin.castLT]
      · congr 1
        simp [Fin.ext_iff]
        omega
    · refine ⟨fun i => if h : i.val = 0 then true else x ⟨i.val - 1, by omega⟩, ?_⟩
      convert hx using 2
      ext ⟨i, hi⟩
      simp only [Fin.append, Fin.addCases]
      split_ifs <;> simp_all <;> try omega
      · exfalso
        simp_all [Fin.castLT]
      · congr 1
        simp [Fin.ext_iff]
        omega
end CircuitComplexity
