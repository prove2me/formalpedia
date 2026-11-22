-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.exists_long_solution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:02.283843+00:00
-- url     : https://prove2.me/submissions/bc8082a0-25c2-49c2-bee8-5e6c7701c51e

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
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_Sat_add_const
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_exists_sat_nonneg_bounded
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
theorem _root_.solution [Finite ι] (D : DifferenceSystem ι)
    (h : ¬ D.HasPositiveCycle) (lower : ι → ℕ) :
    ∃ L : ι → ℕ, D.Sat (fun i => (L i : ℤ)) ∧ ∀ i, lower i ≤ L i := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨x, hx, hb⟩ := D.exists_sat_nonneg_bounded h
  refine ⟨fun i => (x i).toNat + Finset.univ.sup lower, ?_, fun i => ?_⟩
  · have := hx.add_const ((Finset.univ.sup lower : ℕ) : ℤ)
    intro i j c hc
    have h1 := this i j c hc
    have h2 := (hb i).1
    have h3 := (hb j).1
    simp only [Nat.cast_add, Int.toNat_of_nonneg h2, Int.toNat_of_nonneg h3]
    exact h1
  · have := Finset.le_sup (f := lower) (Finset.mem_univ i)
    change lower i ≤ (x i).toNat + Finset.univ.sup lower
    omega
end DeciSigma1.Arithmetic.DifferenceSystem
