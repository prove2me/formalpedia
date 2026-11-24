-- Prove2me | solution 1 for BalanceSpecification.bsm_zero_entropy_characterization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:41.623026+00:00
-- url     : https://prove2.me/submissions/9c824ac2-d21a-4fd6-ab1e-df20d3b6526a

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_Results
public import Theorems.Thm_BalanceSpecification_bsm_iff_finite_periodic_carrier_of_entropy_zero
public import Theorems.Thm_BalanceSpecification_irreducible_bsm_iff_single_periodic_orbit_of_entropy_zero


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty)
    (hh : entropy X hX = 0) :
    (BoundedlySupermultiplicative (language X) ↔
      X.carrier.Finite ∧ ∀ x ∈ X.carrier,
        ∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x) ∧
    ((Irreducible X ∧ BoundedlySupermultiplicative (language X)) ↔
      ∃ x ∈ X.carrier,
        (∃ p : ℕ, 0 < p ∧ SymbolicDynamics.FullShift.shift (p : ℤ) x = x) ∧
        X.carrier = {y | ∃ n : ℕ, SymbolicDynamics.FullShift.shift (n : ℤ) x = y}) :=
  ⟨bsm_iff_finite_periodic_carrier_of_entropy_zero hX hh,
    irreducible_bsm_iff_single_periodic_orbit_of_entropy_zero hX hh⟩
end BalanceSpecification
