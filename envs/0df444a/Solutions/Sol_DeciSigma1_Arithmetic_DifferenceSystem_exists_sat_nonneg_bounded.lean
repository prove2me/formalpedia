-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.exists_sat_nonneg_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:36.269966+00:00
-- url     : https://prove2.me/submissions/4b43770e-4208-436e-822b-f7f1b8a08a5a

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_exists_sat_nonneg_of_no_positiveCycle

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}
namespace DeciSigma1.Arithmetic.DifferenceSystem
theorem _root_.solution [Fintype ι] (h : ¬ D.HasPositiveCycle) :
    ∃ x, D.Sat x ∧ ∀ i, 0 ≤ x i ∧ x i ≤ (Fintype.card ι : ℤ) * D.maxNonnegativeWeight := by
  obtain ⟨x, hx, hb⟩ := exists_sat_nonneg_of_no_positiveCycle h
  refine ⟨x, hx, fun i => ⟨(hb i).1, (hb i).2.trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (by positivity)
end DeciSigma1.Arithmetic.DifferenceSystem
