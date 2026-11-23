-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.wtGe_mul_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:06.291119+00:00
-- url     : https://prove2.me/submissions/b0515e04-9de1-4cd9-92e9-c868116a01f7

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
theorem _root_.solution {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {f : MvPowerSeries ι K}
    (hf : WtGe pi r wt f) {k : ℕ} (hk : ‖(k : K)‖ ≤ pi) :
    WtGe pi r (wt + 1) (f * (k : MvPowerSeries ι K)) := by
  intro n
  have hfn := hf n
  unfold MonoWtGe at hfn ⊢
  first
    | rw [show (k : MvPowerSeries ι K) = MvPowerSeries.C (k : K) from (map_natCast _ k).symm,
        MvPowerSeries.coeff_mul_C, norm_mul]
    | rw [← map_natCast (MvPowerSeries.C (σ := ι) (R := K)) k, MvPowerSeries.coeff_mul_C, norm_mul]
  calc _ ≤ pi ^ (wt - dot n r) * pi := mul_le_mul hfn hk (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = pi ^ (wt + 1 - dot n r) := by
      rw [show wt + 1 - dot n r = (wt - dot n r) + 1 by ring, Real.rpow_add_one h0.ne']
end Formalism.DworkPowerSeriesWeights
