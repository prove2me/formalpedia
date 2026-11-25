-- Prove2me | solution 1 for Formalism.UG.Final.TjEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:11.977605+00:00
-- url     : https://prove2.me/submissions/f1879888-b382-4d1c-92df-61f279b53130

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
private theorem Tj_eq_dosetInd_diagJ {L : Type} [Field L] (O : Subring L) (ϖ : L) (k : Type) [CommRing k]
    (n j : ℕ) (d : GL (Fin n) L) (hd : (d : Matrix (Fin n) (Fin n) L) = diagJ n ϖ j) :
    Tj k n O ϖ j = dosetInd k (GLint (Fin n) O) d := by
  unfold Tj dosetInd
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨a, ha, b, hb, Units.ext (by simp [h, hd])⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, by simp [hd]⟩
end Formalism.UG.Final
end

set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.Final
namespace Formalism.UG.Final
theorem _root_.solution : Formalism.UG.TjEq := by
  intro L _ O ϖ k _ n j d hd
  exact Tj_eq_dosetInd_diagJ O ϖ k n j d hd
end Formalism.UG.Final
