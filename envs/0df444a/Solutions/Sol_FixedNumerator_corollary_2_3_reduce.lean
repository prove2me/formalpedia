-- Prove2me | solution 1 for FixedNumerator.corollary_2_3_reduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:14.36781+00:00
-- url     : https://prove2.me/submissions/6292b38a-7150-447b-92a6-0a7bb21ea7ca

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_QuarticData_truncSum_reduce_num


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (D : QuarticData) (W : GaussianInt → ℂ) (π γ μ' β : GaussianInt)
    (hβ : IsPrimary β) (e X : ℕ) :
    truncSum D W (π ^ e * μ') β (π * γ) X = truncSum D W (π ^ (e % 4) * μ') β (π * γ) X :=
  D.truncSum_reduce_num W μ' β hβ e X
end FixedNumerator
