-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.gmap_loc_eq_of_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:59:26.733807+00:00
-- url     : https://prove2.me/submissions/ad485f2e-10ca-4a2a-818a-ac4261f4e6e6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsHermSemilocalLocRing
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnimodularOfMemGenusOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_smul_mem_loc
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_smul
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_idem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_dualAt
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {p : Ideal (𝓞 K)} (hp : p.IsPrime) (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) {n : ℕ} {e : Fin n → V}
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hge : ∀ i, g (e i) ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p (Submodule.span (𝓞 K) (Set.range e))) =
      Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  have hg' : ∀ u v, h (g u) (g v) = h u v := hg
  have hint : ∀ x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L, ∀ y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L,
      h y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
    intro x hx
    rw [← Formalism.HermitianLatticesTheory.locDual_mem_dualAt]
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hu
    rw [hu]
    exact hx
  have hexp : ∀ v : V, v = ∑ i, h (e i) v • e i := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range e) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      simp only [he, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_ite_eq' Finset.univ j]
      simp
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [map_add, add_smul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | smul a x _ hx =>
      simp only [map_smul, smul_eq_mul, mul_smul]
      rw [← Finset.smul_sum, ← hx]
  apply le_antisymm
  · intro z hz
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hz
    obtain ⟨s, hs, hsx⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hz
    have hall : ∀ v ∈ Submodule.span (𝓞 K) (Set.range e), g v ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hge j
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [Formalism.HermitianLatticesTheory.isomAct_smul]; exact Submodule.smul_mem _ a hx
    have h1 := hall _ hsx
    rw [Formalism.HermitianLatticesTheory.isomAct_smul, LinearEquiv.apply_symm_apply] at h1
    have h2 : z ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) p) (Formalism.HermitianLatticesTheory.loc (K := K) p L) :=
      Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨s, hs, h1⟩
    unfold Formalism.HermitianLatticesTheory.loc at h2 ⊢
    rwa [Formalism.HermitianLatticesTheory.locBasic_locS_idem] at h2
  · intro m hm
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, hexp (g.symm m)]
    refine Submodule.sum_mem _ fun i _ => ?_
    apply smul_mem_loc hp
    · have := hint m hm _ (hge i)
      rwa [← hg', LinearEquiv.apply_symm_apply]
    · exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)
end Formalism.HermitianLattices.Ext.L3.WA
