-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.J.map_smul_hermL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:30.613012+00:00
-- url     : https://prove2.me/submissions/c9a1aab5-8974-4ffc-9987-e430cd3b1aa7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_symF_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mul_mem_pK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.J
namespace Formalism.HermitianLattices.Ext.L3.D2.J
theorem _root_.solution (A : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0)
    (hδ1 : δ ∈ pK K 𝔭 0) (hδ2 : δ⁻¹ ∈ pK K 𝔭 0) :
    (hermL A 𝔭 k).map (DistribSMul.toAddMonoidHom (V →ₗ⋆[K] V →ₗ[K] K) δ) =
      sesqL A 𝔭 k ⊓ (symF (K := K) (V := V)).ker := by
  ext s
  constructor
  · rintro ⟨t, ⟨ht, ht'⟩, rfl⟩
    refine ⟨fun x hx y hy => ?_, ?_⟩
    · have := mul_mem_pK h𝔭 hδ1 (ht' x hx y hy)
      rw [zero_add] at this
      simpa using this
    · show symF _ = 0
      ext x y
      rw [symF_apply]
      simp only [DistribSMul.toAddMonoidHom_apply, LinearMap.smul_apply, smul_eq_mul,
        star_mul', ht y x, hδ, LinearMap.zero_apply]
      ring
  · rintro ⟨hs, hs'⟩
    replace hs' : symF s = 0 := hs'
    have hsk : ∀ x y, star (s x y) = - s y x := fun x y => by
      have := congrArg (fun u => u y x) hs'
      simp only [symF_apply, LinearMap.zero_apply] at this
      exact (neg_eq_of_add_eq_zero_right this).symm
    refine ⟨δ⁻¹ • s, ⟨fun x y => ?_, fun x hx y hy => ?_⟩, ?_⟩
    · simp only [LinearMap.smul_apply, smul_eq_mul, star_mul', star_inv₀, hδ, hsk x y]
      rw [inv_neg]
      ring
    · have := mul_mem_pK h𝔭 hδ2 (hs x hx y hy)
      rw [zero_add] at this
      simpa using this
    · simp only [DistribSMul.toAddMonoidHom_apply]
      rw [smul_smul, mul_inv_cancel₀ hδ0, one_smul]
end Formalism.HermitianLattices.Ext.L3.D2.J
