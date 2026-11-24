-- Prove2me | solution 1 for Formalism.L2.Host.unrAE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:16.524078+00:00
-- url     : https://prove2.me/submissions/1d43af1a-c158-4824-945f-4a4281407607

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAEPf
import Theorems.Thm_Formalism_L2_Host_eq_one_of_pow_near
import Theorems.Thm_Formalism_L2_Host_finiteSingle_mem
import Theorems.Thm_Formalism_L2_Host_mem_integers_of_isUnitAt
import Theorems.Thm_Formalism_L2_Host_isUnitAt_inv
import Theorems.Thm_Formalism_L2_Host_isUnitAt_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.L2.Host
theorem _root_.solution (L : Type) [Field L] [NumberField L] : UnrAE L := by
  intro χ hχ
  set U : Set (Ideles L) := {a | ‖((χ a : ℂˣ) : ℂ) - 1‖ < 1 / 2} with hUdef
  have hUo : IsOpen U :=
    isOpen_lt ((Units.continuous_val.comp hχ).sub continuous_const).norm continuous_const
  have hU1 : (1 : Ideles L) ∈ U := by
    show ‖((χ 1 : ℂˣ) : ℂ) - 1‖ < 1 / 2
    rw [map_one, Units.val_one, sub_self, norm_zero]
    norm_num
  obtain ⟨W, hWo, hWU⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hUo
  have hW1 : Units.embedProduct _ (1 : Ideles L) ∈ W := by
    rw [← Set.mem_preimage, hWU]
    exact hU1
  rw [map_one] at hW1
  obtain ⟨W1, hW1n, W2, hW2n, hprod⟩ := mem_nhds_prod_iff.mp (hWo.mem_nhds hW1)
  have hW2' : MulOpposite.op ⁻¹' W2 ∈ nhds (1 : AdeleRing (𝓞 L) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW2n
  have hV : W1 ∩ MulOpposite.op ⁻¹' W2 ∈ nhds ((1 : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)) :=
    Filter.inter_mem hW1n hW2'
  obtain ⟨Vi, hVi, Vf, hVf, hVprod⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨S, hS, hSV⟩ := finiteSingle_mem Vf hVf
  have key : ∀ v, v ∉ S → ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → localIdele L v x ∈ U := by
    intro v hv x hx
    have hin : ∀ y : (v.adicCompletion L)ˣ, IsUnitAt v y →
        ((localIdele L v y : Ideles L) : AdeleRing (𝓞 L) L) ∈ W1 ∩ MulOpposite.op ⁻¹' W2 := fun y hy =>
      hVprod ⟨mem_of_mem_nhds hVi, hSV v hv _ (mem_integers_of_isUnitAt hy)⟩
    have h1 := hin x hx
    have h2 := hin x⁻¹ (isUnitAt_inv hx)
    rw [← hWU, Set.mem_preimage, Units.embedProduct_apply]
    refine hprod ⟨h1.1, ?_⟩
    have h3 := h2.2
    rw [map_inv] at h3
    exact h3
  refine (hS.subset ?_ : {v | ¬ _}.Finite)
  intro v hv
  by_contra hvS
  apply hv
  intro x hx
  have hpow : ∀ n : ℕ, ‖((χ (localIdele L v x) : ℂˣ) : ℂ) ^ n - 1‖ < 1 / 2 := fun n => by
    have h' : ‖((χ (localIdele L v (x ^ n)) : ℂˣ) : ℂ) - 1‖ < 1 / 2 := key v hvS (x ^ n) (isUnitAt_pow hx n)
    rwa [map_pow, map_pow, Units.val_pow_eq_pow_val] at h'
  exact Units.ext (eq_one_of_pow_near hpow)
end Formalism.L2.Host
