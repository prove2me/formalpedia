-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:22.85229+00:00
-- url     : https://prove2.me/submissions/d1aa4e35-cbbd-4c67-a7e8-b31d5ed879bb

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key


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
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (B : ℕ) (hB : ¬ l ∣ B) :
    1 ≤ ‖(B : K)‖ := by
  have hcop : Nat.Coprime l B := (Nat.Prime.coprime_iff_not_dvd hl).2 hB
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : (u : K) * (l : K) + (v : K) * (B : K) = 1 := by
    have := congrArg (fun z : ℤ => (z : K)) huv
    push_cast at this
    exact this
  have hu : ‖(u : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K u
  have hv : ‖(v : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K v
  have key : ‖(1 : K)‖ ≤ max ‖(u : K) * (l : K)‖ ‖(v : K) * (B : K)‖ := by
    rw [← h1]
    exact IsUltrametricDist.norm_add_le_max _ _
  rw [norm_one, norm_mul, norm_mul] at key
  have hl0 : 0 ≤ ‖(l : K)‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖(B : K)‖ := norm_nonneg _
  have hA : ‖(u : K)‖ * ‖(l : K)‖ < 1 := by
    calc ‖(u : K)‖ * ‖(l : K)‖ ≤ 1 * ‖(l : K)‖ := mul_le_mul_of_nonneg_right hu hl0
      _ < 1 := by rw [one_mul]; exact hl1
  have hC : ‖(v : K)‖ * ‖(B : K)‖ ≤ ‖(B : K)‖ := by
    calc ‖(v : K)‖ * ‖(B : K)‖ ≤ 1 * ‖(B : K)‖ := mul_le_mul_of_nonneg_right hv hB0
      _ = ‖(B : K)‖ := one_mul _
  rcases le_max_iff.1 key with h | h
  · linarith
  · linarith
end Formalism.DworkPowerSeriesWeights
