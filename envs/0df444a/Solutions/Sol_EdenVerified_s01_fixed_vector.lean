-- Prove2me | solution 1 for EdenVerified.s01_fixed_vector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:33.404408+00:00
-- url     : https://prove2.me/submissions/6251810b-ff97-4159-93e8-b0e4a113f314

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_limsup_exteriorGrowthRate
import Theorems.Thm_Eden_tendsto_exteriorGrowthRate


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (p : PhaseSpace) (k : ℕ)
    (v : ExteriorSpace k) (hv : v ≠ 0) :
    Tendsto (fun t : ℝ => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop
      (𝓝 (exteriorGrowthRate k c p v)) ∧
    limsup (fun t : ℝ => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop =
      exteriorGrowthRate k c p v :=
  ⟨tendsto_exteriorGrowthRate c p hv, limsup_exteriorGrowthRate c p hv⟩
end EdenVerified
