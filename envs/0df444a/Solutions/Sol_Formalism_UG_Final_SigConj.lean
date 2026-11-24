-- Prove2me | solution 1 for Formalism.UG.Final.SigConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:55:35.807084+00:00
-- url     : https://prove2.me/submissions/d484ee9f-f0ac-4e1b-b280-8f978b7478c3

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
theorem _root_.solution : Formalism.UG.SigConj := by
  intro n _ _ J p q e P hP g
  have hmul : ∀ A B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ,
      cT (starRingEnd ℂ) (A * B) = cT (starRingEnd ℂ) B * cT (starRingEnd ℂ) A := by
    intro A B
    ext i j
    simp [cT, Matrix.mul_apply, mul_comm]
  have hone : cT (starRingEnd ℂ) (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := by
    simp only [cT]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hPPi : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := Units.mul_inv P
  have hCiC : cT (starRingEnd ℂ) ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 1 := by
    rw [← hmul, hPPi, hone]
  show cT (starRingEnd ℂ) (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = J.reindex e e ↔
    cT (starRingEnd ℂ) ((P⁻¹ * g * P : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * Jpq p q *
      ((P⁻¹ * g * P : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q
  rw [← hP]
  simp only [Units.val_mul, hmul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT (starRingEnd ℂ) ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) (cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)),
    hCiC, Matrix.one_mul, ← Matrix.mul_assoc (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ), hPPi, Matrix.one_mul]
  constructor
  · intro h
    have h2 := congrArg (fun Z => cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * (Z * (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ))) h
    simpa only [Matrix.mul_assoc] using h2
  · intro h
    have h2 := congrArg (fun Z => cT (starRingEnd ℂ) ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * Z *
      ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) h
    simp only [← Matrix.mul_assoc, hCiC, Matrix.one_mul] at h2
    simp only [Matrix.mul_assoc, hPPi, Matrix.mul_one] at h2
    exact h2
end Formalism.UG.Final
