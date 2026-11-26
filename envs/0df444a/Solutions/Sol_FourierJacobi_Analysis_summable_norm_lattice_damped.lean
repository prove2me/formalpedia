-- Prove2me | solution 1 for FourierJacobi.Analysis.summable_norm_lattice_damped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:18:46.700535+00:00
-- url     : https://prove2.me/submissions/335489d1-8f44-42e4-adbc-b2b3b3f0535b

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_weightedLatticeTerm


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hT₀ : 0 < T) (hT₁ : T < 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1) :
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
      ‖weightedLatticeTerm q a b d T p‖) := by
  apply summable_norm_weightedLatticeTerm q T a b d hq ha hb hT₀.le hT₁.le hd₀ hd₁
  have ht := inverseSqrt_pos (show 1 < q by linarith)
  nlinarith
end FourierJacobi.Analysis
