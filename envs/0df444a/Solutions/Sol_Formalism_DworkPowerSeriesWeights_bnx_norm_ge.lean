-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_norm_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:26.775531+00:00
-- url     : https://prove2.me/submissions/b27f30e8-5dfa-45cb-b629-bb05cbb096bc

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_norm_one

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (B : ℕ) (hB0 : B ≠ 0)
    (hB : ¬ l ^ 2 ∣ B) : ‖(l : K)‖ ≤ ‖(B : K)‖ := by
  by_cases hd : l ∣ B
  · obtain ⟨B', rfl⟩ := hd
    have hB' : ¬ l ∣ B' := fun h => hB (by rw [pow_two]; exact mul_dvd_mul_left l h)
    rw [Nat.cast_mul, norm_mul]
    have h1 := bnx_norm_one hl hl1 B' hB'
    have h0 : 0 ≤ ‖(l : K)‖ := norm_nonneg _
    nlinarith
  · have h1 := bnx_norm_one hl hl1 B hd
    linarith
end Formalism.DworkPowerSeriesWeights
