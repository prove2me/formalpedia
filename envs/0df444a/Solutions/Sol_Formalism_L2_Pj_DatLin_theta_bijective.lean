-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.theta_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:17.806802+00:00
-- url     : https://prove2.me/submissions/de124445-258d-4052-8bbd-45712e3c5e64

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatTheta
import Theorems.Thm_Formalism_L2_Pj_DatLin_theta_tmul
import Theorems.Thm_Formalism_L2_Pj_DatLin_phiI_tmul
import Theorems.Thm_Formalism_L2_Pj_DatLin_phiI_bijective
import Theorems.Thm_Formalism_L2_Pj_DatLin_flat_real
import Theorems.Thm_Formalism_L2_Pj_DatLin_exists_den
import Theorems.Thm_Formalism_L2_Pj_DatLin_kap_spec
import Theorems.Thm_Formalism_L2_Pj_DatLin_iota1_repr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open NumberField TensorProduct
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis ι E V) (Ψ : Finset (E →+* ℂ)) (M : Submodule (𝓞 E) V)
variable {Ψ}
variable {b M}
variable (b M)
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ)
    (hfg : Module.Finite (𝓞 E) M) (hsm : ∀ v : V, ∃ s ∈ (𝓞 E)⁰, s • v ∈ M) :
    Function.Bijective (theta b Ψ M) := by
  classical
  have hne : ∀ s ∈ (𝓞 E)⁰, ∀ τ : Ψ, (τ : E →+* ℂ) (algebraMap (𝓞 E) E s) ≠ 0 := by
    intro s hs τ
    rw [map_ne_zero]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  constructor
  ·
    obtain ⟨s, hs, hsI⟩ := exists_den (b := b) hfg
    let κ := (kap b M s hsI).toIntLinearMap
    have hκ : Function.Injective κ := by
      intro v w h
      apply Subtype.ext
      apply b.repr.injective
      ext i
      have h1 := congrArg (fun n => algebraMap (𝓞 E) E (n i)) h
      simp only [κ, AddMonoidHom.coe_toIntLinearMap, kap_spec] at h1
      exact mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs) h1
    have hκR : Function.Injective (LinearMap.baseChange ℝ κ) := by
      have := flat_real
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap κ hκ
    have E2 : ∀ t τ i, phiI Ψ (LinearMap.baseChange ℝ κ t) τ i =
        (τ : E →+* ℂ) (algebraMap (𝓞 E) E s) * theta b Ψ M t τ i := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => intro τ i; simp
      | tmul x v =>
        intro τ i
        simp only [LinearMap.baseChange_tmul, phiI_tmul, theta_tmul, κ,
          AddMonoidHom.coe_toIntLinearMap]
        rw [show ((kap b M s hsI v i : 𝓞 E) : E) = algebraMap (𝓞 E) E (kap b M s hsI v i) from rfl,
          kap_spec, map_mul]
        ring
      | add x y hx hy => intro τ i; simp only [map_add, Pi.add_apply, hx, hy, mul_add]
    intro t t' h
    apply hκR
    apply (phiI_bijective hΨ).1
    funext τ i
    rw [E2, E2, h]
  ·
    choose sf hsf hsfM using hsm
    let s' : 𝓞 E := ∏ i, sf (b i)
    have hs' : s' ∈ (𝓞 E)⁰ := prod_mem fun i _ => hsf (b i)
    have hs'M : ∀ i, s' • b i ∈ M := by
      intro i
      have : s' = sf (b i) * ∏ k ∈ Finset.univ.erase i, sf (b k) :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
      rw [this, mul_comm, mul_smul]
      exact M.smul_mem _ (hsfM (b i))
    let ι₁ := (iota1 b M s' hs'M).toIntLinearMap
    have E1 : ∀ t τ i, theta b Ψ M (LinearMap.baseChange ℝ ι₁ t) τ i =
        (τ : E →+* ℂ) (algebraMap (𝓞 E) E s') * phiI Ψ t τ i := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => intro τ i; simp
      | tmul x n =>
        intro τ i
        simp only [LinearMap.baseChange_tmul, phiI_tmul, theta_tmul, ι₁,
          AddMonoidHom.coe_toIntLinearMap]
        rw [iota1_repr, map_mul]
        rw [show ((n i : 𝓞 E) : E) = algebraMap (𝓞 E) E (n i) from rfl]
        ring
      | add x y hx hy => intro τ i; simp only [map_add, Pi.add_apply, hx, hy, mul_add]
    intro u
    obtain ⟨t, ht⟩ := (phiI_bijective (ι := ι) hΨ).2
      (fun τ i => ((τ : E →+* ℂ) (algebraMap (𝓞 E) E s'))⁻¹ * u τ i)
    refine ⟨LinearMap.baseChange ℝ ι₁ t, ?_⟩
    funext τ i
    rw [E1, ht]
    simp only
    rw [← mul_assoc, mul_inv_cancel₀ (hne s' hs' τ), one_mul]
end Formalism.L2.Pj.DatLin
