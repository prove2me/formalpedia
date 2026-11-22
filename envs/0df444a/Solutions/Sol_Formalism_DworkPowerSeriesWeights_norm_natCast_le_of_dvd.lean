-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.norm_natCast_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:28.129976+00:00
-- url     : https://prove2.me/submissions/8f02574b-e0a0-4696-a56c-e1573c4ac911

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [NormedField K] {ι : Type v}
variable [IsUltrametricDist K]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l k : ℕ} (h : l ∣ k) : ‖(k : K)‖ ≤ ‖(l : K)‖ := by
  obtain ⟨m, rfl⟩ := h
  rw [Nat.cast_mul, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  first
    | exact IsUltrametricDist.norm_natCast_le_one K m
    | exact IsUltrametricDist.norm_natCast_le_one (R := K) m
end Formalism.DworkPowerSeriesWeights
