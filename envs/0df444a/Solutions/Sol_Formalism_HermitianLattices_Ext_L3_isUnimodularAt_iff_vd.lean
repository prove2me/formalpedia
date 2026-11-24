-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.isUnimodularAt_iff_vd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:46.580847+00:00
-- url     : https://prove2.me/submissions/aab55b9f-06b5-482b-86c6-fc96306a4c24

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_idem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_h_smul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_h_smul_right
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_aniso_of_totPosDef
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_det_smul_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_discrIdeal_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_gram
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_orth_unit_frame
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_isUnitIn_algebraMap_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_isUnitIn_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_isUnitIn_prod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_linearIndependent_of_gram_det_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locRing_local
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_not_le_of_vd_eq_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_star_gram_det
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_vd_eq_zero_of_not_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_conjO_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_ne_zero_of_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isHermSemilocal_locRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isSelfDualMod_loc
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_conjIdeal_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_hcompl_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_coe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h P L ↔ vd h L (P.comap (algebraMap (𝓞 F) (𝓞 K))) = 0 := by
  have hPp := hP.isPrime
  have hda := LocF.aniso_of_totPosDef hd
  have hEP : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P := Ideal.map_comap_le
  constructor
  · intro hu
    apply LocF.vd_eq_zero_of_not_le
    obtain ⟨x, hxM, hxo, hxu⟩ := LocF.exists_orth_unit_frame (WA.isHermSemilocal_locRing hK hP)
      (LocF.locRing_local hPp) hs hda (WA.isSelfDualMod_loc hL hPp hu)
    choose s hs' hsx using fun i => Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp
      (show x i ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) P) L from hxM i)
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi (fun i => s i • x i) hsx
    have hmem : g.det ∈ discrIdeal h L := Ideal.subset_span ⟨_, hsx, hdet⟩
    have hunit : WA.IsUnitIn (WA.locRing P) (algebraMap (𝓞 K) K g.det) := by
      rw [hdet]
      have hdiag : (Matrix.of fun i j => h (s i • x i) (s j • x j)) = Matrix.diagonal fun i =>
          star (algebraMap (𝓞 K) K (s i)) * algebraMap (𝓞 K) K (s i) * h (x i) (x i) := by
        ext i j
        rw [Matrix.of_apply, Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right]
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq]
          ring
        · rw [Matrix.diagonal_apply_ne _ hij, hxo i j hij]
          ring
      rw [hdiag, Matrix.det_diagonal]
      apply LocF.isUnitIn_prod
      intro i _
      refine LocF.isUnitIn_mul (LocF.isUnitIn_mul ?_ ?_) (hxu i)
      · rw [← WA.algebraMap_conjO, LocF.isUnitIn_algebraMap_iff hPp]
        exact WA.conjO_mem_hcompl (hs' i)
      · rw [LocF.isUnitIn_algebraMap_iff hPp]
        exact hs' i
    have hnP : g.det ∉ P :=
      ((WA.mem_hcompl_iff hPp _).mp ((LocF.isUnitIn_algebraMap_iff hPp _).mp hunit)).1
    exact fun hle => hnP (hEP (hle hmem))
  · intro h0
    have hn := LocF.not_le_of_vd_eq_zero (LocF.discrIdeal_ne_bot hda hL hLi)
      (ne_top_of_le_ne_top hP.ne_top hEP) h0
    unfold discrIdeal at hn
    rw [Ideal.span_le, Set.not_subset] at hn
    obtain ⟨z, ⟨x, hx, hz⟩, hzn⟩ := hn
    have hzfix : conjO K z = z := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      change star (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K z
      rw [hz, LocF.star_gram_det h hs]
    obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF z).mp hzfix
    have hzP : z ∉ P := by
      intro hmem
      apply hzn
      rw [← ht] at hmem ⊢
      exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr hmem)
    have hzc : z ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
      rw [WA.mem_hcompl_iff hPp, WA.mem_conjIdeal_iff, hzfix]
      exact ⟨hzP, hzP⟩
    have hz0 : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0 := by
      rw [← hz]
      exact WA.algebraMap_ne_zero_of_mem_hcompl hPp hzc
    have hspan : Submodule.span K (Set.range x) = ⊤ :=
      (LocF.linearIndependent_of_gram_det_ne_zero h x hz0).span_eq_top_of_card_eq_finrank'
        (by simp)
    obtain ⟨g, hg, hdet⟩ := LocF.exists_gram hLi x hx
    have hgz : g.det = z := RingOfIntegers.ext (hdet.trans hz.symm)
    obtain ⟨hA, hB⟩ := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs (fun r => ⟨conjO K r, rfl⟩) L hL.fg).1
      P hPp
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
    rw [hB, ← hA]
    apply le_antisymm
    · have hle : Formalism.HermitianLatticesTheory.dual h L ≤ Formalism.HermitianLatticesTheory.loc (K := K) P L := by
        intro y hy
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
        exact Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨g.det, hgz ▸ hzc,
          LocF.det_smul_mem h x hx hspan g hg y (fun i => hy _ (hx i))⟩
      calc Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.dual h L)
          ≤ Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.loc (K := K) P L) :=
            Formalism.HermitianLatticesTheory.locBasic_locS_mono _ hle
        _ = Formalism.HermitianLatticesTheory.loc (K := K) P L := Formalism.HermitianLatticesTheory.locBasic_locS_idem _ _
    · apply Formalism.HermitianLatticesTheory.locBasic_locS_mono
      intro y hy
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      exact fun w hw => hLi w hw y hy
end Formalism.HermitianLattices.Ext.L3
