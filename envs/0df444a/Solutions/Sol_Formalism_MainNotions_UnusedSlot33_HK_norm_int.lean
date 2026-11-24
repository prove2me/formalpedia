-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.norm_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:19.279489+00:00
-- url     : https://prove2.me/submissions/c6fdbed3-421c-4866-8801-99d4fe60c997

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_norm_K
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
theorem _root_.solution (x : 𝓞 H.K) :
    ((Algebra.intNorm ℤ (𝓞 H.K) x : ℤ) : H.E) =
      ((x : H.K) : H.E) * H.conj ((x : H.K) : H.E) := by
  rw [← norm_K H (x : H.K), ← Algebra.coe_norm_int, Algebra.intNorm_eq_norm, map_intCast]
end Formalism.MainNotions.UnusedSlot33.HK
