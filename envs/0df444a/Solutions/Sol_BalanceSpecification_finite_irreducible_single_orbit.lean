-- Prove2me | solution 1 for BalanceSpecification.finite_irreducible_single_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:33.282202+00:00
-- url     : https://prove2.me/submissions/8288b618-49fc-4b8b-8711-6b3467e0ffa4

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_periodic_of_finite_carrier
public import Theorems.Thm_BalanceSpecification_exists_shift_eq_of_finite_irreducible

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
omit [Fintype A]
namespace BalanceSpecification
theorem _root_.solution (hfin : X.carrier.Finite)
    (hX : X.carrier.Nonempty) (hirr : Irreducible X) :
    ∃ x ∈ X.carrier,
      (∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x) ∧
      X.carrier = {y | ∃ n : ℕ, SymbolicDynamics.FullShift.shift (n : ℤ) x = y} := by
  obtain ⟨x, hx⟩ := hX
  refine ⟨x, hx, periodic_of_finite_carrier hfin hx, ?_⟩
  ext y
  constructor
  · intro hy
    exact exists_shift_eq_of_finite_irreducible hfin hirr hx hy
  · rintro ⟨n, rfl⟩
    exact X.mapsTo (n : ℤ) hx
end BalanceSpecification
