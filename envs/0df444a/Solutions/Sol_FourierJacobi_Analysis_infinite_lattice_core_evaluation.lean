-- Prove2me | solution 1 for FourierJacobi.Analysis.infinite_lattice_core_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:17.135828+00:00
-- url     : https://prove2.me/submissions/96518787-3197-4ef7-8794-1cdf08af2c0e

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
import Theorems.Thm_FourierJacobi_Analysis_summable_norm_lattice_undamped
import Theorems.Thm_FourierJacobi_Analysis_latticeCore_eq_paperE
import Theorems.Thm_FourierJacobi_Analysis_tendsto_latticeCore_paperE
import Theorems.Thm_FourierJacobi_Analysis_hasSum_weightedLatticeTerm_of_norm
import Theorems.Thm_FourierJacobi_Analysis_paper_denominator_interior_ne_zero


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
    Summable (fun p : Fin 8 × Fin 3 × LatticeIndex =>
      ‖weightedLatticeTerm q a b d 1 p‖) ∧
    HasSum (weightedLatticeTerm q a b d 1) (paperE q a b d) ∧
    paperC q * paperD1 q a b d * paperD2 q a b d ≠ 0 ∧
    Tendsto (latticeCore q a b d) (𝓝[Set.Ioo 0 1] 1) (𝓝 (paperE q a b d)) := by
  have hn := summable_norm_lattice_undamped q a b d hq ha hb hd₀ hd₁
  have he := latticeCore_eq_paperE q a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁
  refine ⟨hn, ?_, ?_, tendsto_latticeCore_paperE q a b d hq ha hb
    hd₀ hd₁ ha₁ hb₁ hab hab₁⟩
  · rw [← he]
    exact hasSum_weightedLatticeTerm_of_norm q 1 a b d hn
  · exact paper_denominator_interior_ne_zero q (by linarith) a b d ha hb hd₀ hd₁
end FourierJacobi.Analysis
