-- Prove2me | solution 1 for BalanceSpecification.bsm_iff_finite_periodic_carrier_of_entropy_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:12.686801+00:00
-- url     : https://prove2.me/submissions/b79fdbd9-83f2-445b-b671-0a8d65356fa7

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_bsm_iff_finite_carrier_of_entropy_zero
public import Theorems.Thm_BalanceSpecification_periodic_of_finite_carrier

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
    BoundedlySupermultiplicative (language X) ↔
      X.carrier.Finite ∧ ∀ x ∈ X.carrier,
        ∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x := by
  constructor
  · intro hbsm
    have hfin := (bsm_iff_finite_carrier_of_entropy_zero hX hh).mp hbsm
    exact ⟨hfin, fun _ hx => periodic_of_finite_carrier hfin hx⟩
  · intro h
    exact (bsm_iff_finite_carrier_of_entropy_zero hX hh).mpr h.1
end BalanceSpecification
