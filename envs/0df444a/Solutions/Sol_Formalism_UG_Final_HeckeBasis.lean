-- Prove2me | solution 1 for Formalism.UG.Final.HeckeBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:20:34.31498+00:00
-- url     : https://prove2.me/submissions/c883b3e0-fb46-4f0c-b070-527269afa902

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
theorem _root_.solution : Formalism.UG.HeckeBasis := by
  intro G _ K k _
  classical
  have hout : ∀ f ∈ Hecke k K, ∀ g : G, (f : G → k) (Quotient.out (DoubleCoset.mk K K g)) = f g := by
    intro f hf g
    obtain ⟨hbi, -⟩ := hf
    obtain ⟨h, hh, c, hc, he⟩ :=
      (DoubleCoset.eq K K g (Quotient.out (DoubleCoset.mk K K g))).mp (Quotient.out_eq _).symm
    rw [he]
    exact hbi ⟨h, hh⟩ ⟨c, hc⟩ g
  have hfin : ∀ f : Hecke k K, (Function.support fun c : ClassSet K K => (f : G → k) (Quotient.out c)).Finite := by
    intro f
    obtain ⟨-, S, hS⟩ := f.2
    apply (S.finite_toSet.image (DoubleCoset.mk K K)).subset
    intro c hc
    obtain ⟨s, hs, a, b, he⟩ := hS _ hc
    refine ⟨s, hs, ?_⟩
    have h1 : DoubleCoset.mk K K s = DoubleCoset.mk K K (Quotient.out c) :=
      (DoubleCoset.eq K K s _).mpr ⟨a, a.2, b, b.2, he⟩
    rw [h1]
    exact Quotient.out_eq c
  have hinv : ∀ φ : ClassSet K K →₀ k, (fun g => φ (DoubleCoset.mk K K g)) ∈ Hecke k K := by
    intro φ
    show (∀ a b : K, ∀ g : G, φ (DoubleCoset.mk K K ((a : G) * g * b)) = φ (DoubleCoset.mk K K g)) ∧
      ∃ S : Finset G, ∀ g : G, φ (DoubleCoset.mk K K g) ≠ 0 → ∃ s ∈ S, ∃ a b : K, g = (a : G) * s * b
    refine ⟨fun a b g => ?_, ⟨φ.support.image Quotient.out, fun g hg => ?_⟩⟩
    · congr 1
      exact ((DoubleCoset.eq K K g _).mpr ⟨a, a.2, b, b.2, rfl⟩).symm
    · refine ⟨Quotient.out (DoubleCoset.mk K K g),
        Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hg), ?_⟩
      obtain ⟨h, hh, c, hc, he⟩ :=
        (DoubleCoset.eq K K g (Quotient.out (DoubleCoset.mk K K g))).mp (Quotient.out_eq _).symm
      refine ⟨⟨h⁻¹, K.inv_mem hh⟩, ⟨c⁻¹, K.inv_mem hc⟩, ?_⟩
      rw [he]
      group
  refine ⟨{ toFun := fun f => Finsupp.ofSupportFinite (fun c => (f : G → k) (Quotient.out c)) (hfin f)
            map_add' := ?_
            map_smul' := ?_
            invFun := fun φ => ⟨fun g => φ (DoubleCoset.mk K K g), hinv φ⟩
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · intro f₁ f₂
    ext c
    simp [Finsupp.ofSupportFinite_coe]
  · intro r f
    ext c
    simp [Finsupp.ofSupportFinite_coe]
  · intro f
    apply Subtype.ext
    funext g
    show (f : G → k) (Quotient.out (DoubleCoset.mk K K g)) = (f : G → k) g
    exact hout f f.2 g
  · intro φ
    ext c
    show φ (DoubleCoset.mk K K (Quotient.out c)) = φ c
    rw [show DoubleCoset.mk K K (Quotient.out c) = c from Quotient.out_eq c]
  · intro f g
    show (f : G → k) (Quotient.out (DoubleCoset.mk K K g)) = (f : G → k) g
    exact hout f f.2 g
end Formalism.UG.Final
