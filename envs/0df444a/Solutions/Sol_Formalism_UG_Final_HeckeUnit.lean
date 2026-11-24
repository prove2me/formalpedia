-- Prove2me | solution 1 for Formalism.UG.Final.HeckeUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:38:30.415503+00:00
-- url     : https://prove2.me/submissions/5f08f8ed-8bf4-43bc-82c8-5ae64a5923a4

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActionLevelMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AutomorphicFormsDecompositionHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeAssoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_ClassSet
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ecompose
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Fcompose
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Ipindep
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Nabladual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Spherical
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SplitUnitaryGroupIso
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_DualWeylModuleStable
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_SatakeDualWeyl_NablaRepApply
import Definitions.Def_Formalism_SatakeDualWeyl_DualWeylRepApply
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
namespace Formalism.UG.Final
private theorem mem_doubleCoset_one_iff_mem {G : Type} [Group G] (K : Subgroup G) (y : G) :
    y ∈ DoubleCoset.doubleCoset (1 : G) (K : Set G) (K : Set G) ↔ y ∈ K := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨h, hh, c, hc, rfl⟩
    simpa using K.mul_mem hh hc
  · intro hy
    exact ⟨y, hy, 1, K.one_mem, by simp⟩
private theorem quotient_out_mem_iff_eq_one {G : Type} [Group G] (K : Subgroup G) (x : G ⧸ K) :
    x.out ∈ K ↔ x = (QuotientGroup.mk (1 : G) : G ⧸ K) := by
  have hx : (QuotientGroup.mk x.out : G ⧸ K) = x := by
    first
      | exact QuotientGroup.out_eq' x
      | exact Quotient.out_eq x
  constructor
  · intro h
    rw [← hx]
    exact QuotientGroup.eq.mpr (by simpa using h)
  · intro h
    have h2 : (QuotientGroup.mk x.out : G ⧸ K) = QuotientGroup.mk 1 := hx.trans h
    simpa using QuotientGroup.eq.mp h2
end Formalism.UG.Final
end

set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.Final
namespace Formalism.UG.Final
theorem _root_.solution : Formalism.UG.HeckeUnit := by
  intro G _ K k _ f hf
  obtain ⟨hbi, -⟩ := hf
  refine ⟨?_, ?_⟩
  · funext g
    unfold conv
    rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K)]
    · have hmem : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := (quotient_out_mem_iff_eq_one K _).mpr rfl
      have h1 : dosetInd k K 1 (QuotientGroup.mk 1 : G ⧸ K).out = 1 := by
        simp [dosetInd, Set.indicator_apply, (mem_doubleCoset_one_iff_mem K _).mpr hmem]
      simp only [h1, one_mul]
      have h2 := hbi ⟨_, K.inv_mem hmem⟩ 1 g
      simpa using h2
    · intro x hx
      have hn : x.out ∉ K := fun h => hx ((quotient_out_mem_iff_eq_one K x).mp h)
      have h0 : dosetInd k K 1 x.out = 0 := by
        simp [dosetInd, Set.indicator_apply, (mem_doubleCoset_one_iff_mem K _).not.mpr hn]
      simp only [h0, zero_mul]
  · funext g
    unfold conv
    rw [finsum_eq_single _ (QuotientGroup.mk g : G ⧸ K)]
    · have hq : (QuotientGroup.mk ((QuotientGroup.mk g : G ⧸ K).out) : G ⧸ K) = QuotientGroup.mk g := by
        first
          | exact QuotientGroup.out_eq' _
          | exact Quotient.out_eq _
      have hk : ((QuotientGroup.mk g : G ⧸ K).out)⁻¹ * g ∈ K := QuotientGroup.eq.mp hq
      have h1 : dosetInd k K 1 (((QuotientGroup.mk g : G ⧸ K).out)⁻¹ * g) = 1 := by
        simp [dosetInd, Set.indicator_apply, (mem_doubleCoset_one_iff_mem K _).mpr hk]
      simp only [h1, mul_one]
      have h2 := hbi 1 ⟨_, K.inv_mem hk⟩ g
      simpa using h2
    · intro x hx
      have hn : x.out⁻¹ * g ∉ K := by
        intro h
        apply hx
        have hq : (QuotientGroup.mk x.out : G ⧸ K) = QuotientGroup.mk g := QuotientGroup.eq.mpr h
        rw [← hq]
        first
          | exact (QuotientGroup.out_eq' x).symm
          | exact (Quotient.out_eq x).symm
      have h0 : dosetInd k K 1 (x.out⁻¹ * g) = 0 := by
        simp [dosetInd, Set.indicator_apply, (mem_doubleCoset_one_iff_mem K _).not.mpr hn]
      simp only [h0, mul_zero]
end Formalism.UG.Final
