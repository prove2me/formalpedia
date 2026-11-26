-- Prove2me | solution 1 for FourierJacobi.Analysis.tendsto_latticeCore_paperE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:24.792431+00:00
-- url     : https://prove2.me/submissions/5a23c2b7-be9d-4433-9656-610ec4a86577

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Theorems.Thm_FourierJacobi_Analysis_latticeCore_eq_paperE
import Theorems.Thm_FourierJacobi_Analysis_tendsto_latticeCore_undamped

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
    Tendsto (latticeCore q a b d) (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (paperE q a b d)) := by
  rw [← latticeCore_eq_paperE q a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁]
  exact tendsto_latticeCore_undamped q a b d hq ha hb hd₀ hd₁
end FourierJacobi.Analysis
