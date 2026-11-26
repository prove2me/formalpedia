-- Prove2me | solution 1 for FourierJacobi.Analysis.corrected_principal_lattice_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:16.09459+00:00
-- url     : https://prove2.me/submissions/4e53b5f9-ff02-42c3-9f08-3e99f5354fcd

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Theorems.Thm_FourierJacobi_Analysis_latticeCore_eq_paperE
import Theorems.Thm_FourierJacobi_Analysis_tendsto_latticeCore_paperE

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt q < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    (2 / ((q : ℂ) + 1) * latticeCore q a b d 1 =
      2 / ((q : ℂ) + 1) * paperE q a b d) ∧
    Tendsto (fun T => 2 / ((q : ℂ) + 1) * latticeCore q a b d T)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (2 / ((q : ℂ) + 1) * paperE q a b d)) := by
  exact ⟨congrArg (fun z => 2 / ((q : ℂ) + 1) * z)
    (latticeCore_eq_paperE q a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁),
    (tendsto_latticeCore_paperE q a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁).const_mul _⟩
end FourierJacobi.Analysis
