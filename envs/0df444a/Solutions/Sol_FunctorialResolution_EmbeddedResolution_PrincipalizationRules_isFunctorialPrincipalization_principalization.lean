-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PrincipalizationRules.isFunctorialPrincipalization_principalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:55.690108+00:00
-- url     : https://prove2.me/submissions/e686d82f-5c34-4fbf-8894-e1c5ab57645f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ConstantCodimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DimensionRecursion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FunctorialPrincipalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationConstruction
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_markedTripleOrderOne_dim
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_markedTripleOrderOne_isAdmissible
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_principalization_toSequenceOfBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_principalization_lastIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_top_iff_support_eq_empty
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsBoundaryDivisorReduction_isPullbackBlowupSequence_of_smooth
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsBoundaryDivisorReduction_isStrictPullbackBlowupSeq_baseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsBoundaryDivisorReduction_isStrictPullbackBlowupSeq_of_smooth_surjective
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsMaxOrderReduction_isPullbackBlowupSequence_baseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsMaxOrderReduction_isPullbackBlowupSequence_of_smooth
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsMaxOrderReduction_isStrictPullbackBlowupSeq_baseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsMaxOrderReduction_isStrictPullbackBlowupSeq_of_smooth_surjective
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedIdealWithBoundary_SameNontrivialBoundary_symm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_isResolution_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_lastIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_toSequenceOfBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_inputLevelData_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_inputLevelData_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_isMaxOrderReduction_outputLevelData
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_nextLevel_maxOrderReduction
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_nextLevel_orderReduction
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_outputLevelData_maxOrderReduction_eq_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_maxContactIdeal_eq_derivIdealSheafIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_orderAtLeastLocus_one_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups
attribute [local simp] FunctorialResolution.EmbeddedResolution.PrincipalizationRules.inputLevelData_succ
attribute [local simp] FunctorialResolution.EmbeddedResolution.PrincipalizationRules.inputLevelData_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.PrincipalizationRules.nextLevel_maxOrderReduction
attribute [local simp] FunctorialResolution.EmbeddedResolution.PrincipalizationRules.nextLevel_orderReduction
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.maxContactIdeal_eq_derivIdealSheafIterate


attribute [local simp] FunctorialResolution.EmbeddedResolution.markedTripleOrderOne_dim
section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace PrincipalizationRules
end PrincipalizationRules
namespace PrincipalizationRules
private theorem markedBlowupSeq_toSequenceOfBlowups_eq_of_le (B : PrincipalizationRules.{u}) (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) {N : ℕ} (h : krullDimSucc X ≤ N) :
    (B.markedBlowupSeq k X p I E).toSequenceOfBlowups
      = ((B.outputLevelData N).maxOrderRed (markedTripleOrderOne k X p I E)).toSequenceOfBlowups := by
  have hs : (B.outputLevelData (krullDimSucc X)).maxOrderRed (markedTripleOrderOne k X p I E)
      = (B.outputLevelData N).maxOrderRed (markedTripleOrderOne k X p I E) :=
    (B.outputLevelData_maxOrderReduction_eq_of_le h (markedTripleOrderOne k X p I E)
      (le_of_eq (markedTripleOrderOne_dim k X p I E))).symm
  exact congrArg (fun s : (markedTripleOrderOne k X p I E).SequenceOfBlowups => s.toSequenceOfBlowups) hs
private theorem markedBlowupSeq_smoothPullback_isPullback (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p'] [AlgebraicGeometry.LocallyOfFiniteType p']
    [AlgebraicGeometry.QuasiCompact p']
    (φ : X' ⟶ X) [AlgebraicGeometry.Smooth φ] (hφ : φ ≫ p = p')
    (hI' : NonzeroOnComponents (I.comap φ))
    (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)) :
    IsPullbackBlowupSequence φ
      (B.markedBlowupSeq k X' p' (I.comap φ) (E.map fun D => D.comap φ)).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc ≤ max (krullDimSucc X) (krullDimSucc X') :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne k X' p' (I.comap φ) (E.map fun D => D.comap φ)).krullDimSucc
      ≤ max (krullDimSucc X) (krullDimSucc X') := le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E (le_max_left (krullDimSucc X) (krullDimSucc X')),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X' p' (I.comap φ) (E.map fun D => D.comap φ)
      (le_max_right (krullDimSucc X) (krullDimSucc X'))]
  exact @IsMaxOrderReduction.isPullbackBlowupSequence_of_smooth
    (fun d => d ≤ max (krullDimSucc X) (krullDimSucc X'))
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).maxOrderRed)
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).orderRed)
    (B.isMaxOrderReduction_outputLevelData hB (max (krullDimSucc X) (krullDimSucc X')))
    (markedTripleOrderOne k X p I E) hV hdimLe X' p' φ
    (inferInstanceAs (AlgebraicGeometry.Smooth φ)) hφ hV' hPY
private theorem markedBlowupSeq_smoothPullback_isStrictPullback (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p'] [AlgebraicGeometry.LocallyOfFiniteType p']
    [AlgebraicGeometry.QuasiCompact p']
    (φ : X' ⟶ X) [AlgebraicGeometry.Smooth φ] [AlgebraicGeometry.Surjective φ]
    (hφ : φ ≫ p = p')
    (hI' : NonzeroOnComponents (I.comap φ))
    (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)) :
    IsStrictPullbackBlowupSeq φ
      (B.markedBlowupSeq k X' p' (I.comap φ) (E.map fun D => D.comap φ)).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc ≤ max (krullDimSucc X) (krullDimSucc X') :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne k X' p' (I.comap φ) (E.map fun D => D.comap φ)).krullDimSucc
      ≤ max (krullDimSucc X) (krullDimSucc X') := le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E (le_max_left (krullDimSucc X) (krullDimSucc X')),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X' p' (I.comap φ) (E.map fun D => D.comap φ)
      (le_max_right (krullDimSucc X) (krullDimSucc X'))]
  exact @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective
    (fun d => d ≤ max (krullDimSucc X) (krullDimSucc X'))
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).maxOrderRed)
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).orderRed)
    (B.isMaxOrderReduction_outputLevelData hB (max (krullDimSucc X) (krullDimSucc X')))
    (markedTripleOrderOne k X p I E) hV hdimLe X' p' φ
    (inferInstanceAs (AlgebraicGeometry.Smooth φ))
    (inferInstanceAs (AlgebraicGeometry.Surjective φ)) hφ hV' hPY
private theorem markedBlowupSeq_baseChange_isPullback (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (K : Type u) [Field K] [CharZero K] (f : k →+* K)
    [AlgebraicGeometry.Smooth
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    [AlgebraicGeometry.LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    [AlgebraicGeometry.QuasiCompact
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    (hI' : NonzeroOnComponents
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))))
    (hE' : InStrictNormalCrossingPosition (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))) :
    IsPullbackBlowupSequence (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))
      (B.markedBlowupSeq K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
        (E.map fun D =>
          D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
    (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
    (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
    (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D =>
        D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E
      (le_max_left (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f)))),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (le_max_right (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))))]
  exact (B.isMaxOrderReduction_outputLevelData hB
      (max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))))).isPullbackBlowupSequence_baseChange
    (markedTripleOrderOne k X p I E) hV hdimLe K f hV' hPY
private theorem markedBlowupSeq_baseChange_isStrictPullback (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (K : Type u) [Field K] [CharZero K] (f : k →+* K)
    [AlgebraicGeometry.Smooth
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    [AlgebraicGeometry.LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    [AlgebraicGeometry.QuasiCompact
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    (hI' : NonzeroOnComponents
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))))
    (hE' : InStrictNormalCrossingPosition (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))) :
    IsStrictPullbackBlowupSeq (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))
      (B.markedBlowupSeq K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
        (E.map fun D =>
          D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
    (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
    (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
    (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D =>
        D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E
      (le_max_left (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f)))),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (le_max_right (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))))]
  exact (B.isMaxOrderReduction_outputLevelData hB
      (max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p
          (specMapOfFieldHom k K f))))).isStrictPullbackBlowupSeq_baseChange
    (markedTripleOrderOne k X p I E) hV hdimLe K f hV' hPY
private theorem markedBlowupSeq_lastIdeal_eq_top (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    (B.markedBlowupSeq k X p I E).lastIdeal = ⊤ := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hP : (markedTripleOrderOne k X p I E).krullDimSucc ≤ krullDimSucc X := le_refl _
  have hres : MarkedSequenceOfBlowups.IsResolution (B.markedBlowupSeq k X p I E) :=
    (B.isMaxOrderReduction_outputLevelData hB (krullDimSucc X)).resolves (markedTripleOrderOne k X p I E) hV hP
  have h1 : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus (B.markedBlowupSeq k X p I E).lastIdeal 1 = ∅ :=
    (MarkedSequenceOfBlowups.isResolution_iff (B.markedBlowupSeq k X p I E)).mp hres
  apply (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr
  apply Set.eq_empty_of_subset_empty
  intro x hx
  have hx' : x ∈ FunctorialResolution.EmbeddedResolution.orderAtLeastLocus (B.markedBlowupSeq k X p I E).lastIdeal 1 :=
    (mem_orderAtLeastLocus_one_iff (B.markedBlowupSeq k X p I E).lastIdeal x).mpr hx
  rw [h1] at hx'
  exact hx'
end PrincipalizationRules
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.PrincipalizationRules
namespace FunctorialResolution.EmbeddedResolution.PrincipalizationRules
theorem _root_.solution (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u}) (hemb : CommutesWithClosedImmersion.{u} B) :
    IsFunctorialPrincipalization (B.principalization hrad) where
  pushforward := by
    intro k _ _ S X pS p _ _ _ _ _ _ j _ hjp c hc hcc I hI hIX hES hEX
    rw [B.principalization_toSequenceOfBlowups hrad k S pS I hI [] hES,
      B.principalization_toSequenceOfBlowups hrad k X p (imageIdealSheaf j I) hIX [] hEX]
    exact hemb k S X pS p j hjp c hc hcc I hI hIX hES hEX
  base_change := by
    intro k _ _ X p _ _ _ I hI E hE K _ _ f _ _ _ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad K
        (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
        (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_baseChange_isPullback hB k X p I hI E hE K f hI' hE'
  base_change_strict := by
    intro k _ _ X p _ _ _ I hI E hE K _ _ f _ _ _ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad K
        (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
        (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_baseChange_isStrictPullback hB k X p I hI E hE K f hI' hE'
  lastIdeal_eq_top := by
    intro k _ _ X p _ _ _ I hI E hE
    rw [B.principalization_lastIdeal hrad k X p I hI E hE]
    exact B.markedBlowupSeq_lastIdeal_eq_top hB k X p I hI E hE
  smooth_pullback := by
    intro k _ _ X p _ _ _ I hI E hE X' p' _ _ _ φ _ hφ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad k X' p' (I.comap φ) hI'
        (E.map fun D => D.comap φ) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_smoothPullback_isPullback hB k X p I hI E hE X' p' φ hφ hI' hE'
  smooth_pullback_strict := by
    intro k _ _ X p _ _ _ I hI E hE X' p' _ _ _ φ _ _ hφ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad k X' p' (I.comap φ) hI'
        (E.map fun D => D.comap φ) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_smoothPullback_isStrictPullback hB k X p I hI E hE X' p' φ hφ hI' hE'
end FunctorialResolution.EmbeddedResolution.PrincipalizationRules
