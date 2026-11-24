-- Prove2me | solution 1 for BalanceSpecification.irreducible_bsm_iff_single_periodic_orbit_of_entropy_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:22.642887+00:00
-- url     : https://prove2.me/submissions/ef8531d1-b3a1-4314-bc66-44b1d49e69a7

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_bsm_iff_finite_carrier_of_entropy_zero
public import Theorems.Thm_BalanceSpecification_finite_irreducible_single_orbit
public import Theorems.Thm_BalanceSpecification_finite_carrier_of_single_periodic_orbit
public import Theorems.Thm_BalanceSpecification_irreducible_of_single_periodic_orbit

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution
    (hX : X.carrier.Nonempty) (hh : entropy X hX = 0) :
    (Irreducible X ∧ BoundedlySupermultiplicative (language X)) ↔
      ∃ x ∈ X.carrier,
        (∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x) ∧
        X.carrier = {y | ∃ n : ℕ, SymbolicDynamics.FullShift.shift (n : ℤ) x = y} := by
  constructor
  · rintro ⟨hirr, hbsm⟩
    exact finite_irreducible_single_orbit
      ((bsm_iff_finite_carrier_of_entropy_zero hX hh).mp hbsm) hX hirr
  · rintro ⟨x, hx, ⟨p, hp, hperiod⟩, horbit⟩
    exact ⟨irreducible_of_single_periodic_orbit hx hp hperiod horbit,
      (bsm_iff_finite_carrier_of_entropy_zero hX hh).mpr
        (finite_carrier_of_single_periodic_orbit hx hp hperiod horbit)⟩
end BalanceSpecification
