-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.absNorm_natK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:45:38.313214+00:00
-- url     : https://prove2.me/submissions/bc93f9e0-8fee-4404-a4f2-0ee4503af3c7

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_norm_int
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnusedSlot33 Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)
namespace Formalism.MainNotions.UnusedSlot33.HK
theorem _root_.solution (N : ℕ) : Ideal.absNorm (Ideal.span {(N : 𝓞 H.K)}) = N ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have h : (Algebra.norm ℤ (N : 𝓞 H.K) : ℤ) = (N : ℤ) ^ 2 := by
    have h1 := norm_int H (N : 𝓞 H.K)
    rw [Algebra.intNorm_eq_norm] at h1
    simp only [map_natCast] at h1
    have h2 : ((Algebra.norm ℤ (N : 𝓞 H.K) : ℤ) : H.E) = (((N : ℤ) ^ 2 : ℤ) : H.E) := by
      rw [h1]
      push_cast
      rw [map_natCast]
      ring
    exact_mod_cast h2
  rw [h, Int.natAbs_pow, Int.natAbs_natCast]
end Formalism.MainNotions.UnusedSlot33.HK
