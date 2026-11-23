-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.succ_dvd_total
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:47.4732+00:00
-- url     : https://prove2.me/submissions/3a42448d-b80a-4352-86a7-7ca916e4d571

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lw_cast_succ

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
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l d : ℕ} (hl : 1 ≤ l) (hd : Even d) {ι : Type*} (n : ι →₀ ℕ)
    (f : ι → ZMod d)
    (h : ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l (f x)) :
    ((l + 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) := by
  have hl' : ((l : ℕ) : ZMod (l + 1)) = -1 := by
    have h : ((l + 1 : ℕ) : ZMod (l + 1)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_add, Nat.cast_one] at h
    linear_combination h
  have h1 : ((l ^ d - 1 : ℕ) : ZMod (l + 1)) = 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, hl', hd.neg_one_pow, Nat.cast_one,
      sub_self]
  obtain ⟨c, hc⟩ := h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 := congrArg (fun z : ℤ => (z : ZMod (l + 1))) hc
  simp only [Int.cast_mul, Int.cast_sum, Int.cast_natCast, lw_cast_succ, mul_one, h1, zero_mul] at h2
  rw [Int.cast_sum]
  simpa only [Int.cast_natCast] using h2
end Formalism.DworkPowerSeriesWeights
