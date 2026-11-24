-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:50:10.221661+00:00
-- url     : https://prove2.me/submissions/30c9b437-f45a-428e-98d6-857c6501df76

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_exists_norm
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_h_smul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_h_smul_right
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_algebraMap_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_aniso_of_totPosDef
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_orth_unit_frame
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_isUnitIn_algebraMap_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_isUnitIn_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locRing_local
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanA_exists_mul_sub_one_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_algebraMap_comp
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_exists_val
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_conjO_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_algebraMap_conjO
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isHermSemilocal_locRing
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_isSelfDualMod_loc
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_hcompl_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_maximal_over
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isUnimodularAt_iff_vd
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (z : Fin (finrank K V) → ↥L) (g : Fin (finrank K V) → 𝓞 K),
      (∀ i j, i ≠ j → h (z i : V) (z j : V) = 0) ∧
      (∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) ∧ ∀ i, g i - 1 ∈ extP K 𝔭 ^ k := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hPp := hP.isPrime
  have hda := LocF.aniso_of_totPosDef hd
  have hu := (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).2 hv
  obtain ⟨x, hxM, hxo, hxu⟩ := LocF.exists_orth_unit_frame (WA.isHermSemilocal_locRing hK hP)
    (LocF.locRing_local hPp) hs hda (WA.isSelfDualMod_loc hL hPp hu)
  choose s hs' hsx using fun i => Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp
    (show x i ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) P) L from hxM i)
  choose u hu' using fun i => MeanB.exists_val hF hs hLi ⟨s i • x i, hsx i⟩
  have hunit : ∀ i, u i ∉ P.comap ι := by
    intro i
    have h1 : WA.IsUnitIn (WA.locRing P) (algebraMap (𝓞 K) K (ι (u i))) := by
      rw [MeanB.algebraMap_comp, ← hu' i]
      show WA.IsUnitIn (WA.locRing P) (h (s i • x i) (s i • x i))
      rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right]
      refine LocF.isUnitIn_mul ?_ (LocF.isUnitIn_mul ?_ (hxu i))
      · rw [← WA.algebraMap_conjO, LocF.isUnitIn_algebraMap_iff hPp]
        exact WA.conjO_mem_hcompl (hs' i)
      · rw [LocF.isUnitIn_algebraMap_iff hPp]
        exact hs' i
    exact ((WA.mem_hcompl_iff hPp _).mp ((LocF.isUnitIn_algebraMap_iff hPp _).mp h1)).1
  choose u' hu'' using fun i => MeanA.exists_mul_sub_one_mem_pow h𝔭 (hunit i) k
  have hunit' : ∀ i, u' i ∉ P.comap ι := by
    intro i hmem
    have h1 : u' i * u i - 1 ∈ P.comap ι := Ideal.pow_le_self (by omega) (hu'' i)
    have h2 := sub_mem (Ideal.mul_mem_right (u i) _ hmem) h1
    rw [sub_sub_cancel] at h2
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  choose c hc using fun i => exists_norm hK hF h𝔭 hk (hunit' i)
  refine ⟨fun i => ⟨c i • s i • x i, L.smul_mem _ (hsx i)⟩, fun i => conjO K (c i) * c i * ι (u i),
    ?_, ?_, ?_⟩
  · intro i j hij
    show h (c i • s i • x i) (c j • s j • x j) = 0
    simp only [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hxo i j hij, mul_zero]
  · intro i
    show h (c i • s i • x i) (c i • s i • x i) = _
    have := hu' i
    simp only at this
    rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, this, map_mul, map_mul,
      WA.algebraMap_conjO, MeanB.algebraMap_comp]
    ring
  · intro i
    have e : conjO K (c i) * c i * ι (u i) - 1 =
        (conjO K (c i) * c i - ι (u' i)) * ι (u i) + ι (u' i * u i - 1) := by
      rw [map_sub, map_mul, map_one]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ (hc i)) ((idealPowerSpanBounds.mem_pow_iff _ _ _).2 (hu'' i))
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
