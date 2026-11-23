-- Prove2me | solution 1 for Formalism.FG.CoefficientBoundsFormalGroupWitt.coeff_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:21.127466+00:00
-- url     : https://prove2.me/submissions/ca503f33-22bc-4011-b90d-a0619e58ccab

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CoefficientBoundsFormalGroupWitt
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.CoefficientBoundsFormalGroupWitt
theorem _root_.solution {ι : Type v} [Fintype ι] {τ : Type w} (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K)
    (M : ι → ι → K) (f : ι → MvPowerSeries τ K) (j : ι) (n : τ →₀ ℕ) :
    MvPowerSeries.coeff n (f j) = MvPowerSeries.coeff n (f j - (p : K)⁻¹ •
        ∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k))) +
      (p : K)⁻¹ * ∑ k, M j k *
        MvPowerSeries.coeff n (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k))) := by
  simp only [map_sub, map_smul, map_sum, smul_eq_mul]
  ring
end Formalism.FG.CoefficientBoundsFormalGroupWitt
