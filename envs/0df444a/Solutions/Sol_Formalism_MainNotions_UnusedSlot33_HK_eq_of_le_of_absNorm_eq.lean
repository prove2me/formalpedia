-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.eq_of_le_of_absNorm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:34:00.612818+00:00
-- url     : https://prove2.me/submissions/0ff4c197-8a00-4db3-8b46-842f4600c0fe

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq

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
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {I J : Ideal (𝓞 K)}
    (hle : I ≤ J) (hI : Ideal.absNorm I ≠ 0) (h : Ideal.absNorm I = Ideal.absNorm J) : I = J := by
  obtain ⟨M, hM⟩ := Ideal.dvd_iff_le.mpr hle
  have h1 : Ideal.absNorm M = 1 := by
    have h2 := congrArg Ideal.absNorm hM
    rw [map_mul, ← h] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hI) (h2.symm.trans (mul_one _).symm)
  rw [Ideal.absNorm_eq_one_iff] at h1
  rw [hM, h1, Ideal.mul_top]
end Formalism.MainNotions.UnusedSlot33.HK
