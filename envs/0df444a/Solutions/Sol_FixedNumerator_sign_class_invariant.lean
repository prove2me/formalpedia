-- Prove2me | solution 1 for FixedNumerator.sign_class_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:16.868236+00:00
-- url     : https://prove2.me/submissions/dea05e1c-f197-489a-9f5b-04701b42c1c4

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_C_sign_congr


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (a b c : GaussianInt) (hb : IsPrimary b)
    (h : (4 : GaussianInt) ∣ a - b) : (-1 : ℂ) ^ C a c = (-1 : ℂ) ^ C b c :=
  C_sign_congr hb h
end FixedNumerator
