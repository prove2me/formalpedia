-- Prove2me | solution 1 for Eden.le_kaplanYorkeIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:36.905004+00:00
-- url     : https://prove2.me/submissions/a8620f4e-e92d-4e4d-8428-8beca8aad625

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ} {k : ℕ} (hk : k ≤ 5)
    (hs : 0 ≤ spectrumPartialSum a k) : k ≤ kaplanYorkeIndex a := by
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hs⟩)
end Eden
