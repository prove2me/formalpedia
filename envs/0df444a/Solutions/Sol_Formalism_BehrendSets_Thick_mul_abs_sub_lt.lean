-- Prove2me | solution 1 for Formalism.BehrendSets.Thick.mul_abs_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:51.31063+00:00
-- url     : https://prove2.me/submissions/97461ab6-5ab0-4ca6-ab26-724d57607830

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_MulAbsSubLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Thick
namespace Formalism.BehrendSets.Thick
theorem _root_.solution {a b c n : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hna : c * a < n) (hnb : c * b < n) : c * |a - b| < n := by
  have h1 : 0 ≤ c * a := mul_nonneg hc ha
  have h2 : 0 ≤ c * b := mul_nonneg hc hb
  rcases abs_cases (a - b) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
  · have : c * (a - b) = c * a - c * b := by ring
    linarith
  · have : c * -(a - b) = c * b - c * a := by ring
    linarith
end Formalism.BehrendSets.Thick
