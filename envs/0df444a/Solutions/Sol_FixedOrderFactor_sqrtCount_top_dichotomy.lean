-- Prove2me | solution 1 for FixedOrderFactor.sqrtCount_top_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:11:35.278573+00:00
-- url     : https://prove2.me/submissions/94ec563d-e81c-42d6-88b0-4e452fa66d94

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_top_dichotomy__7a2906f2d2a7


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {M : ℕ} [NeZero M] {r : ℕ} (hr : r ∣ M) (a : ℕ) :
    sqrtCount M a r = if ∃ h : ZMod M, IsUnit h ∧ h ^ 2 = a ∧ ZMod.castHom hr (ZMod r) h = 1
      then sqrtCount M 1 r else 0 :=
  sqrtCount_top_dichotomy' hr a
end FixedOrderFactor
