-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.vieta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:21.531833+00:00
-- url     : https://prove2.me/submissions/b0c41e94-338a-4e29-bce0-7c7d6e689b99

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_G_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {R : Type*} [CommRing R]
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution [IsDomain R] {a1 a2 a3 a4 a6 l n z1 z2 z3 : R} (hz : z1 ≠ z2)
    (h1 : G a1 a2 a3 a4 a6 z1 (l * z1 + n) = 0) (h2 : G a1 a2 a3 a4 a6 z2 (l * z2 + n) = 0)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0) :
    G a1 a2 a3 a4 a6 z3 (l * z3 + n) = 0 ∧
      c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0 ∧
      c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0 := by
  have k1 := h1
  have k2 := h2
  rw [G_line] at k1 k2
  have k : (z1 - z2) * (c3 a2 a4 a6 l * (z1 ^ 2 + z1 * z2 + z2 ^ 2)
      + c2 a1 a2 a3 a4 a6 l n * (z1 + z2) + c1 a1 a3 a4 a6 l n) = 0 := by
    linear_combination k1 - k2
  have k' := (mul_eq_zero.mp k).resolve_left (sub_ne_zero.mpr hz)
  have e2 : c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0 := by
    linear_combination (z1 + z2) * he1 - k'
  have e3 : c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0 := by
    linear_combination k1 - z1 ^ 2 * he1 + z1 * e2
  refine ⟨?_, e2, e3⟩
  rw [G_line]
  linear_combination z3 ^ 2 * he1 - z3 * e2 + e3
end Formalism.ELL.WeierstrassChordSeries
