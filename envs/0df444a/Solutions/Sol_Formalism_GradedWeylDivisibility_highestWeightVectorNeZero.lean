-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.highestWeightVectorNeZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:14.873814+00:00
-- url     : https://prove2.me/submissions/bf8c61d1-d928-433c-b7d3-a41a786c7d6d

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HighestWeightVectorNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility
open MvPolynomial
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : HWNe := by
  intro R _ _ r n hn ν h
  have key : ∀ (s : ℕ) (hr : s ≤ r) (hs : s ≤ n),
      eval (fun v : Fin r × Fin n => if v.1.val = v.2.val then (1 : R) else 0)
        (lpMinor R s hr hs) = 1 := by
    intro s hr hs
    unfold lpMinor
    rw [RingHom.map_det]
    convert Matrix.det_one (R := R) (n := Fin s)
    ext p q
    simp [RingHom.mapMatrix_apply, Matrix.one_apply, Fin.ext_iff]
  have h2 := congrArg (eval (fun v : Fin r × Fin n => if v.1.val = v.2.val then (1 : R) else 0)) h
  simp [hw, map_prod, map_pow, key] at h2
end Formalism.GradedWeylDivisibility
