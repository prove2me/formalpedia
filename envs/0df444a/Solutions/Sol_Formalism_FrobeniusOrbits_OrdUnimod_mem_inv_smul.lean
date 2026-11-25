-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.OrdUnimod.mem_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:56.21882+00:00
-- url     : https://prove2.me/submissions/48bebcbe-66ae-47a8-9caf-5b2e9c95478c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrdUnimod
import Theorems.Thm_P2M_Formalism_FrobeniusOrbits_OrdUnimod_mem_one_iff__37eb220bc84c
import Theorems.Thm_Formalism_FrobeniusOrbits_OrdUnimod_integ_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_OrdUnimod_smul_ne_bot
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.OrdUnimod
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.OrdUnimod
theorem _root_.solution (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (B : Ideal (𝓞 (hostE ζ a b)))
    (hB : B ≠ ⊥) (y : hostE ζ a b) :
    σ y ∈ ((σ • B : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b))⁻¹ ↔
      y ∈ ((B : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ := by
  have hc : ∀ z : 𝓞 (hostE ζ a b),
      algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) (σ • z) =
        σ (algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) z) := by
    intro z
    first
    | rfl
    | simp
    | exact NumberField.RingOfIntegers.coe_smul _ _
  have h1 : ((σ • B : Ideal (𝓞 (hostE ζ a b))) :
      FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (smul_ne_bot σ B hB)
  have h2 : ((B : Ideal (𝓞 (hostE ζ a b))) :
      FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hB
  rw [FractionalIdeal.mem_inv_iff h1, FractionalIdeal.mem_inv_iff h2]
  constructor
  · intro h z hz
    rw [FractionalIdeal.mem_coeIdeal] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hm : σ • z' ∈ σ • B := by
      first
      | exact Ideal.smul_mem_pointwise_smul σ z' B hz'
      | exact Submodule.smul_mem_pointwise_smul z' σ B hz'
      | exact Set.smul_mem_smul_set hz'
    have := h (algebraMap _ _ (σ • z')) (by
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨σ • z', hm, rfl⟩)
    rw [mem_one_iff'] at this ⊢
    rwa [hc, ← map_mul, integ_iff] at this
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have hv : σ⁻¹ • w' ∈ B := by
      first
      | exact (Ideal.mem_pointwise_smul_iff_inv_smul_mem).mp hw'
      | exact Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hw'
      | (obtain ⟨v, hv, rfl⟩ := hw'; simpa using hv)
    have := h (algebraMap _ _ (σ⁻¹ • w')) (by
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨σ⁻¹ • w', hv, rfl⟩)
    rw [mem_one_iff'] at this ⊢
    have hw2 : w' = σ • (σ⁻¹ • w') := (smul_inv_smul σ w').symm
    rw [hw2, hc, ← map_mul, integ_iff]
    exact this
end Formalism.FrobeniusOrbits.OrdUnimod
