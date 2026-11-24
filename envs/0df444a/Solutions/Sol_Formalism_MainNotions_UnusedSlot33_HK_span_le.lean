-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.span_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:45:39.937181+00:00
-- url     : https://prove2.me/submissions/f3c80df8-c9f7-46a9-a0c5-2dd35af9318e

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_norm_int
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
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
theorem _root_.solution (cc : Ideal (𝓞 H.K)) :
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 H.E)} ≤
      Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc *
        (H.conj • Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc) := by
  rw [Ideal.span_singleton_le_iff_mem]
  have h1 : Ideal.relNorm ℤ cc ≤ Ideal.comap (algebraMap ℤ (𝓞 H.E))
      (Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc *
        (H.conj • Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) cc)) := by
    rw [Ideal.relNorm_apply, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine Ideal.mem_comap.2 ?_
    have h2 : algebraMap ℤ (𝓞 H.E) (Algebra.intNorm ℤ (𝓞 H.K) x) =
        algebraMap (𝓞 H.K) (𝓞 H.E) x *
          (H.conj • algebraMap (𝓞 H.K) (𝓞 H.E) x) := by
      apply RingOfIntegers.coe_injective
      have h3 := norm_int H x
      rw [eq_intCast]
      push_cast
      exact h3
    rw [h2]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hx)
      (Ideal.smul_mem_pointwise_smul _ _ _ (Ideal.mem_map_of_mem _ hx))
  have h3 : ((Ideal.absNorm cc : ℕ) : ℤ) ∈ Ideal.relNorm ℤ cc := by
    rw [Ideal.relNorm_int]
    exact Ideal.mem_span_singleton_self _
  have h4 := h1 h3
  rw [Ideal.mem_comap] at h4
  simpa using h4
end Formalism.MainNotions.UnusedSlot33.HK
