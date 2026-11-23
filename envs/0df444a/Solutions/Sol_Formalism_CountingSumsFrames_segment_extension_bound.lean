-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_extension_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:24.13981+00:00
-- url     : https://prove2.me/submissions/3394c3f6-9efd-4b27-bfba-94e0ecd07bee

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished

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
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SegExtB := by
  intro C La k N₁ b' bLo bHi x hC hLa hk hN hb h1 h2 hde hx
  have hq : 0 ≤ La / k := div_nonneg hLa hk.le
  have hw : 0 ≤ (bHi - bLo) / b' := div_nonneg (by linarith) hb.le
  have e1 : C * N₁ * La / k = C * N₁ * (La / k) := by ring
  have e2 : 2 * (bHi - bLo) / b' = 2 * ((bHi - bLo) / b') := by ring
  rw [e1, e2] at hde
  have hCN : 4 ≤ C * N₁ := by nlinarith
  have h4 : 4 * (La / k) ≤ C * N₁ * (La / k) := mul_le_mul_of_nonneg_right hCN hq
  have hw12 : (bHi - bLo) / b' < 1 / 12 := by linarith
  have hq24 : La / k < 1 / 24 := by linarith
  have hdiff : bHi - bLo < b' / 12 := by
    rw [div_lt_iff₀ hb] at hw12; linarith
  have hx' : x ≤ b' / 12 := by
    have : La * b' / k = (La / k) * b' := by ring
    rw [this] at hx
    nlinarith
  exact ⟨hw12, hq24, by linarith, by linarith, by linarith, by linarith⟩
end Formalism.CountingSumsFrames
