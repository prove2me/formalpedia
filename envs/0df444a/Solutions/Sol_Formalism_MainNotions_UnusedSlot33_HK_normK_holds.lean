-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.normK_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:01:37.849116+00:00
-- url     : https://prove2.me/submissions/c7ee372e-9f30-4d3d-9542-81a80d73483f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_eq_of_le_of_absNorm_eq
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_span_le
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_absNorm_smul
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_absNorm_natK

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
theorem _root_.solution (H : Host R) : NormKH H := by
  intro cc hcc
  have hN : Ideal.absNorm cc ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hcc
  have e1 : Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)} =
      Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E))
        (Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.K)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have e2 : Ideal.absNorm (Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)}) =
      (Ideal.absNorm cc ^ 2) ^ Module.finrank (𝓞 H.K) (𝓞 H.E) := by
    rw [e1, Ideal.absNorm_algebraMap, absNorm_natK]
  symm
  apply eq_of_le_of_absNorm_eq (span_le H cc)
  · rw [e2]
    exact pow_ne_zero _ (pow_ne_zero _ hN)
  · rw [e2, map_mul, absNorm_smul, Ideal.absNorm_algebraMap]
    ring
end Formalism.MainNotions.UnusedSlot33.HK
