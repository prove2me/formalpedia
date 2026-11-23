-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_pow_mod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:53.019823+00:00
-- url     : https://prove2.me/submissions/f5bf8ca2-8d0f-466c-bec7-96281734c55c

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_pow_reduce

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
theorem _root_.solution (l d x y : ℕ) (hl : 3 ≤ l) (hd : 1 ≤ d)
    (h : l ^ x ≡ l ^ y [MOD l ^ d - 1]) : x % d = y % d := by
  have hx := bnx_pow_reduce l d x (by omega)
  have hy := bnx_pow_reduce l d y (by omega)
  have h' : l ^ (x % d) ≡ l ^ (y % d) [MOD l ^ d - 1] := hx.symm.trans (h.trans hy)
  have hxd : x % d < d := Nat.mod_lt _ (by omega)
  have hyd : y % d < d := Nat.mod_lt _ (by omega)
  have hlt : ∀ k, k < d → l ^ k < l ^ d - 1 := by
    intro k hk
    have h1 : l ^ k ≤ l ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : l ^ d = l * l ^ (d - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : 1 ≤ l ^ (d - 1) := Nat.one_le_pow _ _ (by omega)
    have h4 : 3 * l ^ (d - 1) ≤ l * l ^ (d - 1) := Nat.mul_le_mul_right _ hl
    rw [h2]
    generalize l * l ^ (d - 1) = P at h4 ⊢
    generalize l ^ (d - 1) = L at h1 h3 h4
    generalize l ^ k = A at h1 ⊢
    omega
  have heq : l ^ (x % d) = l ^ (y % d) := by
    have h5 := h'
    unfold Nat.ModEq at h5
    rwa [Nat.mod_eq_of_lt (hlt _ hxd), Nat.mod_eq_of_lt (hlt _ hyd)] at h5
  exact Nat.pow_right_injective (by omega : 2 ≤ l) heq
end Formalism.DworkPowerSeriesWeights
