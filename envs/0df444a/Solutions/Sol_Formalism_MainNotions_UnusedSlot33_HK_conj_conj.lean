-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.conj_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:36.574937+00:00
-- url     : https://prove2.me/submissions/d4ab1f80-1d14-4839-b054-fe63cf67f7d6

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_cc_mul_cc
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnusedSlot33 Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)
namespace Formalism.MainNotions.UnusedSlot33.HK
theorem _root_.solution (x : H.E) : H.conj (H.conj x) = x := by
  have h : H.conj * H.conj = 1 := by
    apply H.gal.injective
    rw [map_mul, map_one, show H.gal H.conj = R.cc from H.gal.apply_symm_apply _]
    exact Formalism.MainNotions.UnusedSlot33.HK.cc_mul_cc R.toFrame
  rw [← AlgEquiv.mul_apply, h, AlgEquiv.one_apply]
end Formalism.MainNotions.UnusedSlot33.HK
