-- Prove2me | solution 1 for DeletedPrimes.window_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:16:19.803998+00:00
-- url     : https://prove2.me/submissions/8cdf1a12-ca17-4a5a-941a-a996681990ca

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
import Theorems.Thm_DeletedPrimes_window_root_aux

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ8 : θ < 1 / 8) :
    let u := (1 - Real.sqrt (1 - 8 * θ)) / 2
    u * (1 - u) = 2 * θ ∧ 0 ≤ u ∧ u < 1 / 2 :=
  window_root_aux hθ0 hθ8
end DeletedPrimes
