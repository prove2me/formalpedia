-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_pow_reduce
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:37.924801+00:00
-- url     : https://prove2.me/submissions/9c5843ad-60f6-4358-905b-55260f2c949e

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_FG_InjVAux_Good_pow
import Theorems.Thm_Formalism_LT_CoeffP_Bd_pow


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
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l d x : ℕ) (hl : 1 ≤ l) : l ^ x ≡ l ^ (x % d) [MOD l ^ d - 1] := by
  have h1 : l ^ d ≡ 1 [MOD l ^ d - 1] := by
    have : 1 ≤ l ^ d := Nat.one_le_pow _ _ (by omega)
    exact ((Nat.modEq_iff_dvd' this).2 dvd_rfl).symm
  calc l ^ x = (l ^ d) ^ (x / d) * l ^ (x % d) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (x / d) * l ^ (x % d) [MOD l ^ d - 1] := (h1.pow _).mul_right _
    _ = l ^ (x % d) := by rw [one_pow, one_mul]
end Formalism.DworkPowerSeriesWeights
