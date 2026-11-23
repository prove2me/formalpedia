-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GoodRankMultinomialDepth.pow_succ_dvd_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:13.993383+00:00
-- url     : https://prove2.me/submissions/573a4866-e3c7-403b-9b70-7e791d777143

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.GoodRankMultinomialDepth
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.CountingSumsFrames.GoodRankMultinomialDepth
theorem _root_.solution {π : O} (hπ : Irreducible π) {a : O} {E : ℕ}
    (h : ¬ a ∣ π ^ E) : π ^ (E + 1) ∣ a := by
  by_cases ha : a = 0
  · simp [ha]
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  by_contra hc
  apply h
  have hk : k ≤ E := by
    by_contra hk
    apply hc
    rw [hu]
    exact Dvd.dvd.mul_left (pow_dvd_pow π (not_le.mp hk)) _
  rw [hu]
  exact (Units.mul_left_dvd).mpr (pow_dvd_pow π hk)
end Formalism.CountingSumsFrames.GoodRankMultinomialDepth
