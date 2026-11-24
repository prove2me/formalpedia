-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_natCast_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:33:19.188431+00:00
-- url     : https://prove2.me/submissions/6c115875-ec4b-44bc-84a1-a9a76f74d3d1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_natCast_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_intCast_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hD : DVRHyp v p) {m : ℕ} (h : ¬ p ∣ m) : v (m : K) = 0 := by
  have hc : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hD.prime).mpr h).symm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have e : (a : K) * m + (b : K) * p = 1 := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this
  have h1 := v.map_add ((a : K) * m) ((b : K) * p)
  rw [e, AddValuation.map_one] at h1
  have h01 : (0 : WithTop ℚ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)
  have hbp : 0 < v ((b : K) * p) := by
    rw [v.map_mul, hD.vp]
    exact lt_of_lt_of_le h01 (le_add_of_nonneg_left (v_intCast_nonneg v b))
  have ham : v ((a : K) * m) ≤ 0 := by
    by_contra hc
    push_neg at hc
    exact absurd h1 (not_le.mpr (lt_min hc hbp))
  rw [v.map_mul] at ham
  exact le_antisymm (le_trans (le_add_of_nonneg_left (v_intCast_nonneg v a)) ham)
    (v_natCast_nonneg v m)
end Formalism.MainNotions.PlaneGram
