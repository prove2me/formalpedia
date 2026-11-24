-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.cokernelLengthEqWach_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:55:26.845518+00:00
-- url     : https://prove2.me/submissions/e72d7369-cf19-406a-8a26-2be3582b8efd

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WachCol
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_wachCol_len_transfer
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_wachCol_lift_transfer
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_wachModule_coboundaries_le_cocycles
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_wachModule_finiteCocycles_le_cocycles
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_wachHom_prodMap_mem_cocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : WachCol := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ V V'
    _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' _ _ _ _ _ _ _ L L' F A D D' _ _ _ _ _ _ _ _ _ _
    Bw M W W' Fw cl cl' hp hW hW' hnat
  set S : Submodule O (LatticeCohomology L') := (latticeFiniteCohomology PD L).map F.H1map with hS

  have hZf_le : latticeFiniteCocycles PD L' ≤ latticeCocycles L' := inf_le_left
  let ψ : ↥(latticeFiniteCocycles PD L') →ₗ[O] LatticeCohomology L' := (Submodule.mkQ _) ∘ₗ Submodule.inclusion hZf_le
  have hψr : LinearMap.range ψ = latticeFiniteCohomology PD L' := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]; rfl
  have hψI : (F.ImF PD).comap (latticeFiniteCocycles PD L').subtype = S.comap ψ := by
    ext ⟨c, hc⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      obtain ⟨u, ⟨a, ha, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.1 h
      refine ⟨Submodule.mkQ _ ⟨a, ha.1⟩, ⟨⟨a, ha.1⟩, ha, rfl⟩, ?_⟩
      simp only [ψ, LinearMap.comp_apply, LatHom.H1map, Submodule.mkQ_apply]
      refine (Submodule.Quotient.eq _).2 ?_
      change F.post a - c ∈ latticeCoboundaries L'
      have e : F.post a - c = -b := by rw [← hab]; abel
      rw [e]; exact (latticeCoboundaries L').neg_mem hb
    · rintro ⟨κ, ⟨x, hx, rfl⟩, hκ⟩
      simp only [ψ, LinearMap.comp_apply, LatHom.H1map, Submodule.mkQ_apply] at hκ
      have hb := (Submodule.Quotient.eq _).1 hκ
      change F.post x - c ∈ latticeCoboundaries L' at hb
      refine Submodule.mem_sup.2 ⟨F.post x, ⟨(x : G → V), hx, rfl⟩, c - F.post x, ?_, by abel⟩
      have := (latticeCoboundaries L').neg_mem hb
      rwa [neg_sub] at this

  have hZ' : W'.Zf ≤ W'.Z1 := wachModule_finiteCocycles_le_cocycles W'
  let χ : ↥W'.Zf →ₗ[O] LatticeCohomology L' := cl' ∘ₗ Submodule.inclusion hZ'
  have hχr : LinearMap.range χ = latticeFiniteCohomology PD L' := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]; exact hW'.2
  have hχI : Fw.ImF.comap W'.Zf.subtype = S.comap χ := by
    ext ⟨pr', hpr'⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      obtain ⟨u, ⟨pr, hpr, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.1 h
      have hpr1 : pr ∈ W.Z1 := wachModule_finiteCocycles_le_cocycles W hpr
      have hf1 : Fw.f2 pr ∈ W'.Z1 := wachHom_prodMap_mem_cocycles Fw pr hpr1
      have hb1 : b ∈ W'.Z1 := wachModule_coboundaries_le_cocycles W' hb
      refine ⟨cl ⟨pr, hpr1⟩, ?_, ?_⟩
      · rw [← hW.2]; exact ⟨⟨pr, hpr1⟩, hpr, rfl⟩
      · rw [hnat ⟨pr, hpr1⟩ ⟨Fw.f2 pr, hf1⟩ rfl]
        have e : (⟨pr', hZ' hpr'⟩ : W'.Z1) = ⟨Fw.f2 pr, hf1⟩ + ⟨b, hb1⟩ := by
          apply Subtype.ext
          simp [← hab]
        change _ = cl' ⟨pr', hZ' hpr'⟩
        rw [e, map_add, (hW'.1.2 ⟨b, hb1⟩).2 hb, add_zero]
    · rintro ⟨κ, hκ, hκ'⟩
      rw [← hW.2] at hκ
      obtain ⟨⟨pr, hpr1⟩, hpr, rfl⟩ := hκ
      have hf1 := wachHom_prodMap_mem_cocycles Fw pr hpr1
      rw [hnat ⟨pr, hpr1⟩ ⟨Fw.f2 pr, hf1⟩ rfl] at hκ'
      have h0 : cl' (⟨pr', hZ' hpr'⟩ - ⟨Fw.f2 pr, hf1⟩) = 0 := by
        rw [map_sub]; exact sub_eq_zero.2 hκ'.symm
      have hb := (hW'.1.2 _).1 h0
      exact Submodule.mem_sup.2 ⟨Fw.f2 pr, ⟨pr, hpr, rfl⟩, pr' - Fw.f2 pr, hb, by abel⟩
  have hcolG := wachCol_len_transfer (latticeFiniteCocycles PD L') (F.ImF PD) ψ (latticeFiniteCohomology PD L') S hψr hψI
  have hcolW := wachCol_len_transfer W'.Zf Fw.ImF χ (latticeFiniteCohomology PD L') S hχr hχI
  refine ⟨?_, fun e => ?_⟩
  · unfold LatHom.col Formalism.CoboundaryTransfers.Hom.col
    rw [hcolG, hcolW]
  · have hG := wachCol_lift_transfer (latticeFiniteCocycles PD L') (F.ImF PD) ψ (latticeFiniteCohomology PD L') S hψr hψI
      ((PD.p : O) ^ e)
    have hWl := wachCol_lift_transfer W'.Zf Fw.ImF χ (latticeFiniteCohomology PD L') S hχr hχI ((PD.p : O) ^ e)
    unfold LatHom.LiftF Formalism.CoboundaryTransfers.Hom.LiftF
    rw [hG]
    have hsm : ∀ pr : D' × D', ((Bw.p ^ e : ℕ)) • pr = ((PD.p : O) ^ e) • pr := by
      intro pr
      rw [hp, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
    simp only [hsm]
    exact hWl.symm
end Formalism.WeaklyAdmissibleFiltrations
