-- Prove2me | solution 1 for FixedNumerator.primary_sq_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:09.930131+00:00
-- url     : https://prove2.me/submissions/3b8ba021-8dd6-484b-8074-62bdb30e2750

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_sq_sub_one


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (π : GaussianInt) (hπ : IsPrimary π) :
    (4 : GaussianInt) ∣ π ^ 2 - 1 :=
  sq_sub_one hπ
end FixedNumerator
