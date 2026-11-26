-- Prove2me | solution 1 for FixedNumerator.splitting_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:58.115806+00:00
-- url     : https://prove2.me/submissions/a03fdf81-4598-48cc-9b71-f4e37147f54e

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_QuarticData_g_split


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (D : QuarticData) (μ π c' : GaussianInt) (hπ : IsPrimary π)
    (hc' : IsPrimary c') (hcop : IsCoprime π c') (k : ℕ) :
    D.g μ (π ^ k * c') =
      (-1 : ℂ) ^ C c' (π ^ k) * D.g μ (π ^ k) * D.g (μ * π ^ (2 * k)) c' :=
  D.g_split μ hπ hc' hcop k
end FixedNumerator
