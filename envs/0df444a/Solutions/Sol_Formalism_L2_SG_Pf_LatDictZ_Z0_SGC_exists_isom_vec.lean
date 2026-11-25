-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.SGC.exists_isom_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:19.725436+00:00
-- url     : https://prove2.me/submissions/1dd6c3fb-b065-4814-9560-c3a34b292754

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SemiGenusLocal
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_witt_extension_theorem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Module
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hsy : h.IsSymm) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {e X : V}
    (he : h e e ≠ 0) (hXe : h X X = h e e) :
    ∃ τ : V ≃ₗ[K] V, (∀ x y, h (τ x) (τ y) = h x y) ∧ τ e = X := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hX0 : X ≠ 0 := by rintro rfl; simp at hXe; exact he hXe.symm
  let f : (K ∙ e) →ₗ[K] V := (LinearMap.toSpanSingleton K V X) ∘ₗ
    ((LinearEquiv.coord K V e he0 : (K ∙ e) ≃ₗ[K] K) : (K ∙ e) →ₗ[K] K)
  have hf : ∀ u, f u = LinearEquiv.coord K V e he0 u • X := fun u => rfl
  have hu : ∀ u : (K ∙ e), (u : V) = LinearEquiv.coord K V e he0 u • e := fun u =>
    (LinearEquiv.coord_apply_smul K V e he0 u).symm
  have hinj : Function.Injective f := by
    intro u v huv
    rw [hf, hf] at huv
    have := smul_left_injective K hX0 huv
    exact (LinearEquiv.coord K V e he0).injective this
  have hiso : ∀ u v : (K ∙ e), h (f u) (f v) = h u v := by
    intro u v
    rw [hf, hf, hu u, hu v]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hXe]
  obtain ⟨g, hg, hgf⟩ := witt_extension_theorem K V h (fun x y => hsy.eq x y) hnd (K ∙ e) f hinj hiso
  refine ⟨g, hg, ?_⟩
  have := hgf ⟨e, Submodule.mem_span_singleton_self e⟩
  rw [this, hf, LinearEquiv.coord_self, one_smul]
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
