-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.kap_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:24.163714+00:00
-- url     : https://prove2.me/submissions/a35ed9af-637d-4e23-aa62-b34eb6350316

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (N r B : ℕ) (hr : 1 ≤ r) : (N + 4) * (r * B) + 6 * B ≤ kap N r B := by
  unfold kap
  have h1 : r ≤ r ^ 2 := by nlinarith
  have h2 : B ≤ r * B := Nat.le_mul_of_pos_left B hr
  have h3 : (N + 4) * (r * B) + 6 * B ≤ 10 * (N + 3) * (r * B) := by nlinarith
  have h4 : 10 * (N + 3) * (r * B) ≤ 10 * (N + 3) * r ^ 2 * (B + 1) := by
    have : r * B ≤ r ^ 2 * (B + 1) := by nlinarith
    calc 10 * (N + 3) * (r * B) ≤ 10 * (N + 3) * (r ^ 2 * (B + 1)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  omega
end Formalism.GM.gammaIntegralityLemmas
