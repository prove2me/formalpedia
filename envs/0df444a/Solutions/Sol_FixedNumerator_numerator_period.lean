-- Prove2me | solution 1 for FixedNumerator.numerator_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:47:06.263278+00:00
-- url     : https://prove2.me/submissions/abaaf465-02eb-41ba-8cbe-33f2f1051fd9

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_QuarticData_g_mul_pow_four


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (D : QuarticData) (μ π c : GaussianInt) (hc : IsPrimary c)
    (hcop : IsCoprime π c) (j : ℕ) : D.g (μ * π ^ (4 * j)) c = D.g μ c :=
  D.g_mul_pow_four μ hc hcop j
end FixedNumerator
