-- Prove2me | solution 1 for Eden.exponentSum_image_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:20.637709+00:00
-- url     : https://prove2.me/submissions/25fa7f51-6953-431f-bdab-cac4946288b8

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
import Theorems.Thm_Eden_exponentSum_le_twice_index

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) (k : ℕ) :
    BddAbove ((fun p => spectrumPartialSum (lyapunovExponent c p) k) '' attractor) := by
  refine ⟨(k : ℝ) * 2, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  exact exponentSum_le_twice_index hc p k
end Eden
