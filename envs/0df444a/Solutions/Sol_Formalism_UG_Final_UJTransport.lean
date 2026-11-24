-- Prove2me | solution 1 for Formalism.UG.Final.UJTransport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:39:41.184647+00:00
-- url     : https://prove2.me/submissions/5df6760e-9835-4189-aed0-249223f2f709

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
import Theorems.Thm_Formalism_UG_Final_BCMem
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
theorem _root_.solution : Formalism.UG.UJTransport := by
  intro A B _ _ n _ _ σ σ' φ hφ J
  have hmem : ∀ g : GL n A, g ∈ UJ σ J → bc (φ : A →+* B) g ∈ UJ σ' (J.map φ) :=
    fun g hg => Formalism.UG.Final.BCMem A B n σ σ' (φ : A →+* B) hφ J g hg
  have hψ : ((φ.symm : B ≃+* A) : B →+* A).comp σ' = σ.comp ((φ.symm : B ≃+* A) : B →+* A) := by
    apply RingHom.ext
    intro b
    apply φ.injective
    have h1 := RingHom.congr_fun hφ (φ.symm b)
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply] at h1 ⊢
    rw [h1]
  have hmem' : ∀ h : GL n B, h ∈ UJ σ' (J.map φ) → bc ((φ.symm : B ≃+* A) : B →+* A) h ∈ UJ σ J := by
    intro h hh
    have := Formalism.UG.Final.BCMem B A n σ' σ ((φ.symm : B ≃+* A) : B →+* A) hψ (J.map φ) h hh
    have hJ : (J.map φ).map ((φ.symm : B ≃+* A) : B →+* A) = J := by
      ext i j
      simp
    rw [hJ] at this
    exact this
  refine ⟨{ toFun := fun g => ⟨bc (φ : A →+* B) g, hmem g g.2⟩
            invFun := fun h => ⟨bc ((φ.symm : B ≃+* A) : B →+* A) h, hmem' h h.2⟩
            left_inv := fun g => ?_
            right_inv := fun h => ?_
            map_mul' := fun g h => ?_ }, fun g => rfl⟩
  · apply Subtype.ext
    apply Units.ext
    ext i j
    simp [bc]
  · apply Subtype.ext
    apply Units.ext
    ext i j
    simp [bc]
  · apply Subtype.ext
    simp
end Formalism.UG.Final
