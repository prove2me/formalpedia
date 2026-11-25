-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exponent_eq_orderAlongComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:54:05.949516+00:00
-- url     : https://prove2.me/submissions/da31b425-026c-446a-a46b-be2387a8446e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplittingUniqueness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_of_stalkIdeal_eq_maximalIdeal_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_prod_of_isMonomialOnOpen
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_genericPoint_eq_of_isMonomialSplitting
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exponent_le_orderAlongComponent
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_closure_genericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_genericPoint_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_genericPoint_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_coordBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_tensorKaehlerBasis_mapBaseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_orderAlongComponent_eq_orderAt_genericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealSheafColon_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_ne_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_monomialFactorIdeal_genericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_ne_top_of_nonzeroOnComponents
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_genericPoint_eq_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialFactorIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialPartAlongDivisor_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
import Theorems.Thm_Ideal_list_prod_le_getElem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.coordBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.tensorKaehlerBasis_mapBaseChange
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.idealSheafColon_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def
attribute [local simp] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
private theorem ideal_listProd_le_mul_getElem_of_lt {R : Type*} [CommRing R] (L : List (Ideal R)) :
    ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length), i < j →
      L.prod ≤ (L[i]'hi) * (L[j]'hj) := by
  induction L with
  | nil =>
      intro i _ hi _ _
      simp at hi
  | cons A L ih =>
      intro i j hi hj hij
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd hij (lt_irrefl 0)
          | succ j' =>
              have hj' : j' < L.length := by simpa using hj
              simp only [List.prod_cons, List.getElem_cons_zero, List.getElem_cons_succ]
              exact Ideal.mul_mono le_rfl (Ideal.list_prod_le_getElem L j' hj')
      | succ i' =>
          cases j with
          | zero => exact absurd hij (Nat.not_lt_zero _)
          | succ j' =>
              have hi' : i' < L.length := by simpa using hi
              have hj' : j' < L.length := by simpa using hj
              simp only [List.prod_cons, List.getElem_cons_succ]
              exact le_trans (le_trans Ideal.mul_le_inf inf_le_right)
                (ih i' j' hi' hj' (by omega))
private theorem ideal_listProd_le_mul_getElem_of_ne {R : Type*} [CommRing R] (L : List (Ideal R))
    (i j : ℕ) (hi : i < L.length) (hj : j < L.length) (hij : i ≠ j) :
    L.prod ≤ (L[i]'hi) * (L[j]'hj) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ideal_listProd_le_mul_getElem_of_lt L i j hi hj h
  · rw [mul_comm]
    exact ideal_listProd_le_mul_getElem_of_lt L j i hj hi h
private theorem ideal_listProd_le_pow_add {R : Type*} [CommRing R] (m : Ideal R)
    (L : List (Ideal R)) (i j : ℕ) (hi : i < L.length) (hj : j < L.length) (hij : i ≠ j)
    (b c : ℕ) (hbi : (L[i]'hi) ≤ m ^ b) (hcj : (L[j]'hj) ≤ m ^ c) :
    L.prod ≤ m ^ (b + c) := by
  refine le_trans (ideal_listProd_le_mul_getElem_of_ne L i j hi hj hij) ?_
  rw [pow_add]
  exact Ideal.mul_mono hbi hcj
private theorem ideal_listProd_finRange_eq_of_ne_eq_top {R : Type*} [CommRing R] {n : ℕ}
    (f : Fin n → Ideal R) (j : Fin n) (h : ∀ l : Fin n, l ≠ j → f l = ⊤) :
    ((List.finRange n).map f).prod = f j := by
  rw [← Fin.prod_univ_def]
  refine Finset.prod_eq_single j (fun l _ hl => ?_) (fun hj => absurd (Finset.mem_univ j) hj)
  rw [h l hl, Ideal.one_eq_top]
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k : Type u} [Field k] [CharZero k]
    [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    (U : X.Opens) (a : Fin E.length → ℕ) (ha : IsMonomialOnOpen E M U a)
    (j : Fin E.length) {C : Set X} (hC : IsIrreducibleComponentOfSupport (E.get j) C)
    (x : X) (hxU : x ∈ U) (hxC : x ∈ C) :
    a j = orderAlongComponent I hC.isIrreducible := by
  have hD : E.get j ∈ E := by simp
  have hxcl : x ∈ closure ({hC.isIrreducible.genericPoint} : Set X) := by
    rw [hC.closure_genericPoint]
    exact hxC
  have hηU : hC.isIrreducible.genericPoint ∈ U := by
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hxcl (U : Set X) U.isOpen hxU
    rw [Set.mem_singleton_iff] at hz
    rw [← hz]
    exact hzU
  have hηC : hC.isIrreducible.genericPoint ∈ C := hC.genericPoint_mem
  have hlocj : IsEtaleLocallyCoordinateDivisor p (E.get j) :=
    isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E.get j) hD
  have hjmax : stalkIdeal (E.get j) hC.isIrreducible.genericPoint ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal (E.get j)
      hC.isIrreducible.genericPoint).mp hC.genericPoint_mem_support
  have hmemj : stalkIdeal (monomialPartAlongDivisor I (E.get j)) hC.isIrreducible.genericPoint =
      stalkIdeal (E.get j) hC.isIrreducible.genericPoint ^
        orderAlongComponent I hC.isIrreducible :=
    stalkIdeal_monomialPartAlongDivisor_of_mem p I hlocj hC hηC
  have hbj : stalkIdeal (monomialPartAlongDivisor I (E.get j)) hC.isIrreducible.genericPoint ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^
        orderAlongComponent I hC.isIrreducible := by
    rw [hmemj]
    exact Ideal.pow_right_mono hjmax _
  have hPstalk : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D) hC.isIrreducible.genericPoint)).prod :=
    stalkIdeal_monomialFactorIdeal E I hC.isIrreducible.genericPoint
  have hPord : orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (orderAlongComponent I hC.isIrreducible : ℕ∞) :=
    orderAt_monomialFactorIdeal_genericPoint p E I hE hI hD hC
  have hzero : ∀ l : Fin E.length, l ≠ j →
      stalkIdeal (E.get l) hC.isIrreducible.genericPoint ^ a l = ⊤ := by
    intro l hlj
    by_cases hs : hC.isIrreducible.genericPoint ∈ ((E.get l).support : Set X)
    · have hal : a l = 0 := by
        obtain ⟨C', hC', hηC'⟩ :=
          exists_isIrreducibleComponentOfSupport (E.get l) hC.isIrreducible.genericPoint hs
        have hDl : E.get l ∈ E := by simp
        have hlocl : IsEtaleLocallyCoordinateDivisor p (E.get l) :=
          isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E.get l) hDl
        have hle : a l ≤ orderAlongComponent I hC'.isIrreducible :=
          exponent_le_orderAlongComponent p E hE hI hsplit U a ha l hC'
            hC.isIrreducible.genericPoint hηU hηC'
        have hmeml : stalkIdeal (monomialPartAlongDivisor I (E.get l)) hC.isIrreducible.genericPoint =
            stalkIdeal (E.get l) hC.isIrreducible.genericPoint ^
              orderAlongComponent I hC'.isIrreducible :=
          stalkIdeal_monomialPartAlongDivisor_of_mem p I hlocl hC' hηC'
        have hlmax : stalkIdeal (E.get l) hC.isIrreducible.genericPoint ≤
            IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
          (mem_support_iff_stalkIdeal_le_maximalIdeal (E.get l)
            hC.isIrreducible.genericPoint).mp hs
        have hbl : stalkIdeal (monomialPartAlongDivisor I (E.get l)) hC.isIrreducible.genericPoint ≤
            IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^ a l := by
          rw [hmeml]
          exact le_trans (Ideal.pow_right_mono hlmax _) (Ideal.pow_le_pow_right hle)
        have hjlen : (j : ℕ) <
            (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
              hC.isIrreducible.genericPoint)).length := by
          simp
        have hllen : (l : ℕ) <
            (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
              hC.isIrreducible.genericPoint)).length := by
          simp
        have hjne : (j : ℕ) ≠ (l : ℕ) := by
          intro hv
          apply hlj
          ext
          exact hv.symm
        have hgj : (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
            hC.isIrreducible.genericPoint))[(j : ℕ)]'hjlen =
            stalkIdeal (monomialPartAlongDivisor I (E.get j)) hC.isIrreducible.genericPoint := by
          simp
        have hgl : (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
            hC.isIrreducible.genericPoint))[(l : ℕ)]'hllen =
            stalkIdeal (monomialPartAlongDivisor I (E.get l)) hC.isIrreducible.genericPoint := by
          simp
        have hPle : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint ≤
            IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^
              (orderAlongComponent I hC.isIrreducible + a l) := by
          rw [hPstalk]
          refine ideal_listProd_le_pow_add _ _ (j : ℕ) (l : ℕ) hjlen hllen hjne _ _ ?_ ?_
          · rw [hgj]
            exact hbj
          · rw [hgl]
            exact hbl
        have hord : ((orderAlongComponent I hC.isIrreducible + a l : ℕ) : ℕ∞) ≤
            orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint :=
          (le_orderAt_iff (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
            (orderAlongComponent I hC.isIrreducible + a l)).mpr hPle
        rw [hPord] at hord
        have hnat : orderAlongComponent I hC.isIrreducible + a l ≤
            orderAlongComponent I hC.isIrreducible := by exact_mod_cast hord
        omega
      rw [hal, pow_zero, Ideal.one_eq_top]
    · have hstop : stalkIdeal (E.get l) hC.isIrreducible.genericPoint = ⊤ := by
        by_contra hcon
        exact hs ((mem_support_iff_stalkIdeal_ne_top (E.get l)
          hC.isIrreducible.genericPoint).mpr hcon)
      rw [hstop, ← Ideal.one_eq_top, one_pow]
  have hprod : stalkIdeal M hC.isIrreducible.genericPoint =
      ((List.finRange E.length).map
        (fun i => stalkIdeal (E.get i) hC.isIrreducible.genericPoint ^ a i)).prod :=
    stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a ha hC.isIrreducible.genericPoint hηU
  have hMstalk : stalkIdeal M hC.isIrreducible.genericPoint =
      stalkIdeal (E.get j) hC.isIrreducible.genericPoint ^ a j := by
    rw [hprod]
    exact ideal_listProd_finRange_eq_of_ne_eq_top
      (fun i => stalkIdeal (E.get i) hC.isIrreducible.genericPoint ^ a i) j hzero
  have hmaxj : stalkIdeal (E.get j) hC.isIrreducible.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    stalkIdeal_genericPoint_eq_maximalIdeal p (E.get j) hlocj hC.isIrreducible
      hC.subset_support hC.maximal
  have hMI : orderAt M hC.isIrreducible.genericPoint =
      orderAt I hC.isIrreducible.genericPoint :=
    orderAt_genericPoint_eq_of_isMonomialSplitting p E hE hI hsplit hD hC
  have hfin : orderAt M hC.isIrreducible.genericPoint ≠ ⊤ := by
    rw [hMI]
    exact orderAt_ne_top_of_nonzeroOnComponents I hI hC.isIrreducible.genericPoint
  have hMord : orderAt M hC.isIrreducible.genericPoint = (a j : ℕ∞) :=
    orderAt_eq_of_stalkIdeal_eq_maximalIdeal_pow M hC.isIrreducible.genericPoint (a j)
      (by rw [hMstalk, hmaxj]) hfin
  have hco : (orderAlongComponent I hC.isIrreducible : ℕ∞) =
      orderAt I hC.isIrreducible.genericPoint := coe_orderAlongComponent_eq_orderAt_genericPoint hC hI
  have hfinal : ((a j : ℕ) : ℕ∞) = ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞) := by
    rw [← hMord, hMI, ← hco]
  exact_mod_cast hfinal
end FunctorialResolution.EmbeddedResolution
