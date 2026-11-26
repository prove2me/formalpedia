-- Prove2me | solution 1 for FixedNumerator.sign_even_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:27.654433+00:00
-- url     : https://prove2.me/submissions/a445d47f-1e0d-469d-8e4f-c1585c20913e

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_C_sign_even_pow


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (π a : GaussianInt) (hπ : IsPrimary π) (k : ℕ) (hk : Even k) :
    (-1 : ℂ) ^ C a (π ^ k) = 1 :=
  C_sign_even_pow hπ a hk
end FixedNumerator
