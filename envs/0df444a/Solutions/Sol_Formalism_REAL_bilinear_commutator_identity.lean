-- Prove2me | solution 1 for Formalism.REAL.bilinear_commutator_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:58.888189+00:00
-- url     : https://prove2.me/submissions/2feb7706-b393-4b03-ae2e-84ba1a85c39a

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] (p1 b1 p2 b2 d1 d2 : A)
    (h1 : b1 * p2 - p2 * b1 = d1) (h2 : b2 * p1 - p1 * b2 = d2)
    (hp : p1 * p2 = p2 * p1) (hb : b1 * b2 = b2 * b1)
    (hd1 : p1 * d1 = d1 * p1) (hd2 : p2 * d2 = d2 * p2) :
    p1 * b1 * (p2 * b2) - p2 * b2 * (p1 * b1) = d1 * (p1 * b2) - d2 * (p2 * b1) := by
  have e1 : b1 * p2 = p2 * b1 + d1 := by rw [← h1]; abel
  have e2 : b2 * p1 = p1 * b2 + d2 := by rw [← h2]; abel
  calc p1 * b1 * (p2 * b2) - p2 * b2 * (p1 * b1)
      = p1 * (b1 * p2) * b2 - p2 * (b2 * p1) * b1 := by simp only [mul_assoc]
    _ = p1 * (p2 * b1 + d1) * b2 - p2 * (p1 * b2 + d2) * b1 := by rw [e1, e2]
    _ = p1 * p2 * (b1 * b2) + p1 * d1 * b2 - (p2 * p1 * (b2 * b1) + p2 * d2 * b1) := by
        simp only [mul_add, add_mul, mul_assoc]
    _ = d1 * (p1 * b2) - d2 * (p2 * b1) := by
        rw [hp, hb, hd1, hd2]
        simp only [mul_assoc]
        abel
end Formalism.REAL
