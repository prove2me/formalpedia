-- Prove2me | solution 1 for FixedOrderFactor.sqrtCount_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:11:24.014221+00:00
-- url     : https://prove2.me/submissions/506f7c5c-9e60-4749-9cfa-bc71cb54aee6

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_top__6ac6750b47a8


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {M : ℕ} [NeZero M] {r : ℕ} (hr : r ∣ M) (a : ℕ) :
    sqrtCount M a r = (Finset.univ.filter fun h : ZMod M =>
      IsUnit h ∧ h ^ 2 = a ∧ ZMod.castHom hr (ZMod r) h = 1).card :=
  sqrtCount_top' hr a
end FixedOrderFactor
