-- Prove2me | solution 1 for Formalism.CountingSumsFrames.depth_le_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:38.656806+00:00
-- url     : https://prove2.me/submissions/2558b3ff-22e2-4b93-aa71-b448f20f090e

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_depth_real_bound

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
theorem _root_.solution {p N N₁ r s t : ℕ} {Y a : ℝ} (hY : 1 ≤ Y) (hr : (3 : ℝ) ≤ (r : ℝ) + 1)
    (hN1 : (1 : ℝ) ≤ N₁) (hts : t ≤ s) (hs : s ≤ N₁) (hlg : 0 ≤ lgSeg p a r) :
    DjSeg p N r s t Y a ≤
      45 * Y ^ 2 * (N₁ : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2 * lgSeg p a r + kap0I p N (r + 1) a := by
  have h := depth_real_bound (T := t) (S := s) (M := N₁) (R := r) (Y := Y) (lg := lgSeg p a r)
    (κ := kapSeg p a r s) (fl := ((⌊Y * firstDepth t Y (kapSeg p a r s)⌋ : ℤ) : ℝ)) hY (by linarith) hN1
    (Nat.cast_nonneg _) (by exact_mod_cast hts) (by exact_mod_cast hs) hlg rfl (Int.floor_le _)
  unfold DjSeg uSeg
  linarith
end Formalism.CountingSumsFrames
