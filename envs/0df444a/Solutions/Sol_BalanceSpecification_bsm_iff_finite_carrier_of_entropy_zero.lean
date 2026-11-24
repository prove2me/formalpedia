-- Prove2me | solution 1 for BalanceSpecification.bsm_iff_finite_carrier_of_entropy_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:25.643964+00:00
-- url     : https://prove2.me/submissions/f3d19525-8ae6-46ba-88c2-9ef72c002528

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_finite_carrier_iff_bounded_wordCount
public import Theorems.Thm_BalanceSpecification_bsm_iff_bounded_wordCount_of_entropy_zero


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty)
    (hh : entropy X hX = 0) :
    BoundedlySupermultiplicative (language X) ↔ X.carrier.Finite := by
  rw [bsm_iff_bounded_wordCount_of_entropy_zero hX hh, finite_carrier_iff_bounded_wordCount]
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨N, hN⟩ := exists_nat_ge C
    refine ⟨N, ?_⟩
    intro n
    have hn := le_trans (hC (Set.mem_range_self n)) hN
    exact_mod_cast hn
  · rintro ⟨C, hC⟩
    refine ⟨(C : ℝ), ?_⟩
    rintro _ ⟨n, rfl⟩
    change (wordCount (language X) n : ℝ) ≤ (C : ℝ)
    exact_mod_cast hC n
end BalanceSpecification
