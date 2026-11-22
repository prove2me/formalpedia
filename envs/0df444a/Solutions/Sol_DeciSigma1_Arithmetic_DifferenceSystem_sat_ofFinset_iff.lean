-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.sat_ofFinset_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:17.080093+00:00
-- url     : https://prove2.me/submissions/a85bd966-b3ee-4f4e-b315-0f4a93934166

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}
namespace DeciSigma1.Arithmetic.DifferenceSystem
theorem _root_.solution [DecidableEq ι] (E : Finset (ι × ι × ℤ)) (x : ι → ℤ) :
    (ofFinset E).Sat x ↔ ∀ e ∈ E, x e.1 + e.2.2 ≤ x e.2.1 := by
  constructor
  · intro h e he
    set s := (E.filter (fun e' => e'.1 = e.1 ∧ e'.2.1 = e.2.1)).image (fun e => e.2.2)
    have hmem : e.2.2 ∈ s := Finset.mem_image.mpr ⟨e, by simp [he], rfl⟩
    obtain ⟨m, hm⟩ := Finset.max_of_mem hmem
    have hle : e.2.2 ≤ m := Finset.le_max_of_eq hmem hm
    have := h e.1 e.2.1 m hm
    linarith
  · intro h i j c hc
    have hmem := Finset.mem_of_max hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨heE, rfl, rfl⟩ := by simpa using he
    exact h e heE
end DeciSigma1.Arithmetic.DifferenceSystem
