-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostUnimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:57:14.076211+00:00
-- url     : https://prove2.me/submissions/e6ad4db2-8eb5-4434-8200-f401b06672a2

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrdUnimod
import Theorems.Thm_Formalism_FrobeniusOrbits_OrdUnimod_mem_inv_smul
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
open OrdUnimod
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostUnimodular := by
  intro e q d _ L _ _ ζ a b _ σ _ 𝔟 h x
  have hd1 : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b)
      (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 := by
    first
    | exact FractionalIdeal.dual_ne_zero _ _ one_ne_zero
    | exact FractionalIdeal.dual_ne_zero one_ne_zero
    | exact FractionalIdeal.dual_ne_zero (𝓞 (KinE ζ a b)) (KinE ζ a b) one_ne_zero
  have hprod : ((𝔟 : Ideal (𝓞 (hostE ζ a b))) :
      FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) *
      ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) =
      (FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b)
        (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ := by
    rw [← FractionalIdeal.coeIdeal_mul, ← h]
    first
    | exact coeIdeal_differentIdeal _ _ _ _
    | exact coeIdeal_differentIdeal (𝓞 (KinE ζ a b)) (KinE ζ a b) (hostE ζ a b) (𝓞 (hostE ζ a b))
    | exact coeIdeal_differentIdeal (A := 𝓞 (KinE ζ a b)) (K := KinE ζ a b) (L := hostE ζ a b)
        (B := 𝓞 (hostE ζ a b))
  have hne : ((𝔟 : Ideal (𝓞 (hostE ζ a b))) :
      FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) *
      ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 := by
    rw [hprod]; exact inv_ne_zero hd1
  have hb := left_ne_zero_of_mul hne
  have hsb := right_ne_zero_of_mul hne
  have hb0 : 𝔟 ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp hb
  have hd : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b)
      (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) =
      (((𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) *
      ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ := by
    rw [hprod, inv_inv]
  have hJ : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b)
      (((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ =
      ((𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b))⁻¹ := by
    rw [FractionalIdeal.dual_eq_mul_inv, hd, inv_inv, mul_inv, mul_assoc, inv_mul_cancel₀ hsb,
      mul_one]
  have hx : ∀ z : hostE ζ a b, z ∈ ((𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b))⁻¹ ↔
      ∀ w ∈ (((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹,
        Algebra.trace (KinE ζ a b) (hostE ζ a b) (z * w) ∈
          (algebraMap (𝓞 (KinE ζ a b)) (KinE ζ a b)).range := by
    intro z
    rw [← hJ, FractionalIdeal.mem_dual (inv_ne_zero hsb)]
    simp only [Algebra.traceForm_apply]
  rw [hx x]
  constructor
  · intro hw y hy
    exact hw _ ((mem_inv_smul σ 𝔟 hb0 y).mpr hy)
  · intro hy w hw
    have hw' : σ (σ.symm w) ∈ (((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ := by
      rw [AlgEquiv.apply_symm_apply]; exact hw
    have := hy (σ.symm w) ((mem_inv_smul σ 𝔟 hb0 _).mp hw')
    rwa [AlgEquiv.apply_symm_apply] at this
end Formalism.FrobeniusOrbits
