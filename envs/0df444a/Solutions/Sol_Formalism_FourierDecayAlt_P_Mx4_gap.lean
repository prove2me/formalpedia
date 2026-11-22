-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.gap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:15.580732+00:00
-- url     : https://prove2.me/submissions/0923f8e6-a20e-4fed-85bb-99729c039724

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_tyInterlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_rhoUp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    (π πl πj : Ty P) (h1 : Up P l π πl) (h2 : Up P j π πj) :
    2 ≤ rho P π j - rho P π l ∨ rho P π j - rho P π l ≤ -2 := by
  have hI := tyInterlaces P hP π
  rcases Nat.lt_or_gt_of_ne hjl with h | h
  · left
    have o := (ord P.k P.u P.u' (rho P π) hI l hl).2.2.1 j hj h
    have b := tyInterlaces P hP πl l hl
    have e := rhoUp P l π πl h1 l hl
    rw [if_pos rfl] at e
    rw [e] at b
    linarith [o.1, b.1]
  · right
    have hIj := tyInterlaces P hP πj
    have o := (ord P.k P.u P.u' (rho P πj) hIj l hl).2.2.2 j hj h
    have b := hI l hl
    have e := rhoUp P j π πj h2 j hj
    rw [if_pos rfl] at e
    rw [e] at o
    linarith [o.1, b.2.2.1]
end Formalism.FourierDecayAlt.P.Mx4
