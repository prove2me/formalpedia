-- Prove2me | solution 1 for FixedNumerator.ddhl_3_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:54.874799+00:00
-- url     : https://prove2.me/submissions/27d9e13d-94a5-4475-98b9-aee2d2a1e388

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_QuarticData_g_mul_sq


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (D : QuarticData) (μ c c' : GaussianInt) (hc : IsPrimary c)
    (hc' : IsPrimary c') (hcc : IsCoprime c c') :
    D.g μ (c * c') = (-1 : ℂ) ^ C c' c * D.g (μ * c' ^ 2) c * D.g μ c' :=
  D.g_mul_sq μ hc hc' hcc
end FixedNumerator
