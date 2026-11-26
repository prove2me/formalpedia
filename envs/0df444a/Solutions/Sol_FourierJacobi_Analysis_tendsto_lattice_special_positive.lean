-- Prove2me | solution 1 for FourierJacobi.Analysis.tendsto_lattice_special_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:10:50.951772+00:00
-- url     : https://prove2.me/submissions/c97acc70-8771-4852-a1da-3ce0a10fb5a1

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Theorems.Thm_FourierJacobi_Analysis_tendsto_positive_zero_product


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (a b : ℂ) :
    Tendsto (fun T => ((1 - (1 : ℂ)) / ((q : ℂ) + 1)) *
      latticeCore q a b (inverseSqrt q : ℂ) T)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 0) :=
  tendsto_positive_zero_product q (latticeCore q a b (inverseSqrt q : ℂ))
end FourierJacobi.Analysis
