-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_central_norm_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:18:48.709939+00:00
-- url     : https://prove2.me/submissions/cc5bfe24-25a1-45fd-a75e-e2b7feb7248d

import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Definitions.Def_FourierJacobi_Analysis_CentralWeylSeries
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_weightedLatticeTerm


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) (r : Fin 3) :
    Summable (fun p : LatticeIndex =>
      ∑ i : Fin 8, ‖weightedLatticeTerm q a b d T (i,r,p)‖) := by
  have hs := summable_norm_weightedLatticeTerm q T a b d hq ha hb hT₀ hT₁ hd₀ hd₁ hstrict
  exact summable_sum (s := Finset.univ) (fun i _ => (hs.prod_factor i).prod_factor r)
end FourierJacobi.Analysis
