-- Prove2me | solution 1 for FourierJacobi.Analysis.hasSum_weightedLatticeTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:18:50.773125+00:00
-- url     : https://prove2.me/submissions/63172411-1439-4931-a99f-94c82fee5283

import Definitions.Def_FourierJacobi_Analysis_I0Master
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I2Master
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_weightedLatticeTerm
import Theorems.Thm_FourierJacobi_Analysis_hasSum_weightedLatticeTerm_of_norm

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) :
    HasSum (weightedLatticeTerm q a b d T) (latticeCore q a b d T) :=
  hasSum_weightedLatticeTerm_of_norm q T a b d
    (summable_norm_weightedLatticeTerm q T a b d hq ha hb hT₀ hT₁ hd₀ hd₁ hstrict)
end FourierJacobi.Analysis
