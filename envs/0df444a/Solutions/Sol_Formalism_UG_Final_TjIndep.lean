-- Prove2me | solution 1 for Formalism.UG.Final.TjIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:18:08.99636+00:00
-- url     : https://prove2.me/submissions/d234dab0-e9c7-42ad-9c39-a859e07b0c6b

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
theorem _root_.solution : Formalism.UG.TjIndep := by
  intro L _ O ϖ u k _ n j hu hu' hu0
  let d : Fin n → O := fun i => if (i : ℕ) < j then ⟨u, hu⟩ else 1
  let d' : Fin n → O := fun i => if (i : ℕ) < j then ⟨u⁻¹, hu'⟩ else 1
  have hdd : ∀ i, d i * d' i = 1 := by
    intro i
    simp only [d, d']
    split_ifs
    · exact Subtype.ext (mul_inv_cancel₀ hu0)
    · exact mul_one 1
  have hd'd : ∀ i, d' i * d i = 1 := fun i => by rw [mul_comm]; exact hdd i
  let D0 : GL (Fin n) O := ⟨Matrix.diagonal d, Matrix.diagonal d',
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hdd]; exact Matrix.diagonal_one,
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hd'd]; exact Matrix.diagonal_one⟩
  let Dg : GL (Fin n) L := bc O.subtype D0
  have hD : (Dg : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < j then u else 1) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases ha : (a : ℕ) < j <;> simp [Dg, D0, d, bc, ha]
    · simp [Dg, D0, bc, hab]
  have hdiag : diagJ n (u * ϖ) j = diagJ n ϖ j * (Dg : Matrix (Fin n) (Fin n) L) := by
    rw [hD]
    simp only [diagJ, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> ring
  have hDmem : Dg ∈ GLint (Fin n) O := MonoidHom.mem_range.mpr ⟨D0, rfl⟩
  unfold Tj
  congr 1
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, Dg * b, (GLint (Fin n) O).mul_mem hDmem hb, ?_⟩
    rw [h, hdiag, Units.val_mul]
    simp only [Matrix.mul_assoc]
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, Dg⁻¹ * b, (GLint (Fin n) O).mul_mem ((GLint (Fin n) O).inv_mem hDmem) hb, ?_⟩
    rw [h, hdiag, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Dg : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.one_mul]
end Formalism.UG.Final
