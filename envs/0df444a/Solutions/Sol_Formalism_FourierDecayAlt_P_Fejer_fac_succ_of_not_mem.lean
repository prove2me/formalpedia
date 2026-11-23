-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fejer.fac_succ_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:12.703819+00:00
-- url     : https://prove2.me/submissions/6695273b-d9dd-4bbd-a776-f7cc933c7773

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FacSuccOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fejer
open Real Finset Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.Fejer
theorem _root_.solution (N : ℕ) (t : ℤ) (ht : t ∉ Finset.Icc (-(N : ℤ)) N) :
    fac (N + 1) t = 0 := by
  rw [Finset.mem_Icc] at ht
  have habs : (N : ℤ) < |t| := by
    by_contra h
    exact ht (abs_le.1 (not_lt.1 h))
  have hz : (((N + 1 : ℕ) : ℤ) - |t|).toNat = 0 := by
    rw [Int.toNat_eq_zero]; push_cast; omega
  unfold fac
  rw [hz]; simp
end Formalism.FourierDecayAlt.P.Fejer
