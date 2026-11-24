-- Prove2me | solution 1 for Formalism.UG.Final.StabStd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:18:12.319221+00:00
-- url     : https://prove2.me/submissions/1f807617-f4ee-4540-a903-545b2e4ecf26

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
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
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
theorem _root_.solution : Formalism.UG.StabStd := by
  intro A R _ _ _ n _ _ hι
  have hL : ∀ x : n → A, x ∈ stdLat (n := n) (A := A) R ↔ ∀ i, ∃ r : R, algebraMap R A r = x i := by
    intro x
    simp [stdLat, Submodule.mem_pi]
  have hfwd : ∀ g0 : GL n R, ∀ x : n → A, x ∈ stdLat (n := n) (A := A) R →
      Matrix.mulVec ((bc (algebraMap R A) g0 : GL n A) : Matrix n n A) x ∈ stdLat (n := n) (A := A) R := by
    intro g0 x hx
    rw [hL] at hx ⊢
    choose r hr using hx
    intro i
    refine ⟨∑ j, (g0 : Matrix n n R) i j * r j, ?_⟩
    simp [Matrix.mulVec, dotProduct, bc, hr]
  apply le_antisymm
  · intro g hg
    have hginv : g⁻¹ ∈ stabGL (stdLat (n := n) (A := A) R) := (stabGL _).inv_mem hg
    have hcol : ∀ h : GL n A, h ∈ stabGL (stdLat (n := n) (A := A) R) →
        ∀ i j, ∃ r : R, algebraMap R A r = (h : Matrix n n A) i j := by
      intro h hh i j
      have he : (Pi.single j 1 : n → A) ∈ stdLat (n := n) (A := A) R := by
        rw [hL]
        intro k
        by_cases hk : k = j
        · subst hk
          exact ⟨1, by simp⟩
        · exact ⟨0, by simp [hk]⟩
      have h2 := (hh _).1 he
      rw [hL] at h2
      obtain ⟨r, hr⟩ := h2 i
      refine ⟨r, ?_⟩
      rw [hr]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    choose M hM using hcol g hg
    choose N hN using hcol g⁻¹ hginv
    have hinj : ∀ X Y : Matrix n n R, X.map (algebraMap R A) = Y.map (algebraMap R A) → X = Y := by
      intro X Y hXY
      ext i j
      exact hι (congrFun (congrFun hXY i) j)
    have hMg : (Matrix.of M).map (algebraMap R A) = (g : Matrix n n A) := by
      ext i j
      simp [hM]
    have hNg : (Matrix.of N).map (algebraMap R A) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j
      simp [hN]
    refine MonoidHom.mem_range.mpr ⟨⟨Matrix.of M, Matrix.of N, hinj _ _ ?_, hinj _ _ ?_⟩, ?_⟩
    · rw [Matrix.map_mul, hMg, hNg, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hMg, hNg, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · apply Units.ext
      exact hMg
  · intro g hg
    obtain ⟨g0, rfl⟩ := MonoidHom.mem_range.mp hg
    intro x
    constructor
    · exact hfwd g0 x
    · intro hx
      have h2 := hfwd g0⁻¹ _ hx
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul] at h2
      simpa using h2
end Formalism.UG.Final
