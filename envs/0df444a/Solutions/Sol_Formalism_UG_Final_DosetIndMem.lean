-- Prove2me | solution 1 for Formalism.UG.Final.DosetIndMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:18:11.096736+00:00
-- url     : https://prove2.me/submissions/ea670bbc-2ded-450b-80af-beda3f59e06b

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



set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.Final
namespace Formalism.UG.Final
theorem _root_.solution : Formalism.UG.DosetIndMem := by
  intro G _ K k _ g
  show (∀ a b : K, ∀ x : G, dosetInd k K g ((a : G) * x * b) = dosetInd k K g x) ∧
    ∃ S : Finset G, ∀ x : G, dosetInd k K g x ≠ 0 → ∃ s ∈ S, ∃ a b : K, x = (a : G) * s * b
  refine ⟨fun a b x => ?_, ⟨{g}, fun x hx => ?_⟩⟩
  · by_cases hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)
    · have hm : (a : G) * x * b ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
        obtain ⟨h, hh, c, hc, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
        exact DoubleCoset.mem_doubleCoset.mpr
          ⟨(a : G) * h, K.mul_mem a.2 hh, c * b, K.mul_mem hc b.2, by simp only [mul_assoc]⟩
      simp [dosetInd, Set.indicator_apply, hx, hm]
    · have hm : (a : G) * x * b ∉ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
        intro hm
        apply hx
        obtain ⟨h, hh, c, hc, he⟩ := DoubleCoset.mem_doubleCoset.mp hm
        refine DoubleCoset.mem_doubleCoset.mpr
          ⟨(a : G)⁻¹ * h, K.mul_mem (K.inv_mem a.2) hh, c * (b : G)⁻¹, K.mul_mem hc (K.inv_mem b.2), ?_⟩
        have hx' : x = (a : G)⁻¹ * ((a : G) * x * b) * (b : G)⁻¹ := by group
        rw [hx', he]
        simp only [mul_assoc]
      simp [dosetInd, Set.indicator_apply, hx, hm]
  · have hm : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
      by_contra h
      apply hx
      simp [dosetInd, Set.indicator_apply, h]
    obtain ⟨h, hh, c, hc, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hm
    exact ⟨g, Finset.mem_singleton_self g, ⟨h, hh⟩, ⟨c, hc⟩, rfl⟩
end Formalism.UG.Final
