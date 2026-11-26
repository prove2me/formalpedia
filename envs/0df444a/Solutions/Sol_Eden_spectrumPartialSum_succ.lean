-- Prove2me | solution 1 for Eden.spectrumPartialSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:29.760604+00:00
-- url     : https://prove2.me/submissions/5f1cf986-7468-4b78-9422-682d13efac7d

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (a : Fin 5 → ℝ) (k : ℕ) :
    spectrumPartialSum a (k + 1) = spectrumPartialSum a k + spectrumEntry a k :=
  Finset.sum_range_succ _ _
end Eden
