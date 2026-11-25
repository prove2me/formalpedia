-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_regularSystemOfParameters_containing_etaleChartCoords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:09.939826+00:00
-- url     : https://prove2.me/submissions/a6949d63-6885-457f-ba1a-e9948a183b5a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoordIdeal_eq_span_image
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoordIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_quotient_map_etaleChartCoordIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_quotient_map_etaleChartCoordIdeal_add_card
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_span_eq_maximalIdeal_card_eq_ringKrullDim (Q : Type u) [CommRing Q] [IsRegularLocalRing Q] :
    ∃ (n : ℕ) (z : Fin n → Q), Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q ∧
      (n : WithBot ℕ∞) = ringKrullDim Q := by
  classical
  have : IsLocalRing Q := inferInstance
  have : IsNoetherianRing Q := inferInstance
  have : Module.Finite (IsLocalRing.ResidueField Q) (IsLocalRing.CotangentSpace Q) :=
    inferInstance
  have hsurjres : Function.Surjective (algebraMap Q (IsLocalRing.ResidueField Q)) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨y, rfl⟩
  set b := Module.finBasis (IsLocalRing.ResidueField Q) (IsLocalRing.CotangentSpace Q) with hb
  have hsurj : Function.Surjective (IsLocalRing.maximalIdeal Q).toCotangent :=
    Ideal.toCotangent_surjective _
  choose w hw using fun i => hsurj (b i)
  have hspanQ : Submodule.span Q (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span (IsLocalRing.ResidueField Q) (Set.range b) := by
      rw [b.span_eq]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Submodule.subset_span hy
    · exact zero_mem _
    · intro y z _ _ hy hz
      exact add_mem hy hz
    · intro c y _ hy
      obtain ⟨c', rfl⟩ := hsurjres c
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ hy
  have himg : ⇑(IsLocalRing.maximalIdeal Q).toCotangent '' (Set.range w) = Set.range b := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hw)
  have hMtop : Submodule.span Q (Set.range w) = ⊤ := by
    refine IsLocalRing.CotangentSpace.map_eq_top_iff.mp ?_
    rw [Submodule.map_span, himg]
    exact hspanQ
  refine ⟨Module.finrank (IsLocalRing.ResidueField Q) (IsLocalRing.CotangentSpace Q),
    fun i => ((w i : Q)), ?_, ?_⟩
  · have h1 : Submodule.map (IsLocalRing.maximalIdeal Q).subtype
        (Submodule.span Q (Set.range w)) = Ideal.span (Set.range fun i => ((w i : Q))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← h1, hMtop, Submodule.map_subtype_top]
  · exact (IsRegularLocalRing.iff_finrank_cotangentSpace Q).mp ‹_›
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ)
    (S : Type u) [CommRing S] [Algebra (CoordPolynomialRing k m) S]
    [Algebra.Etale (CoordPolynomialRing k m) S] (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A]
    [Algebra S A] [IsLocalization q.primeCompl A] [IsLocalRing A] (J₀ : Finset (Fin m))
    (hJ₀ : ∀ j ∈ J₀, etaleChartCoord k m S j ∈ q) :
    ∃ (d : ℕ) (x : Fin d → S),
      (∀ i, x i ∈ q) ∧
      (∀ j ∈ J₀, ∃ i, x i = etaleChartCoord k m S j) ∧
      Ideal.span (Set.range fun i => algebraMap S A (x i)) = IsLocalRing.maximalIdeal A ∧
      (d : WithBot ℕ∞) = ringKrullDim A := by
  classical
  set I := Ideal.map (algebraMap S A) (etaleChartCoordIdeal k m S J₀) with hIdef
  have hreg : IsRegularLocalRing (A ⧸ I) :=
    isRegularLocalRing_quotient_map_etaleChartCoordIdeal k m S q A J₀ hJ₀
  have : IsLocalRing (A ⧸ I) := inferInstance
  obtain ⟨n, z, hzspan, hzdim⟩ := exists_span_eq_maximalIdeal_card_eq_ringKrullDim (A ⧸ I)
  have hIle : I ≤ IsLocalRing.maximalIdeal A := by
    rw [hIdef]
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro s hs
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q s inferInstance).mpr
      (etaleChartCoordIdeal_le k m S J₀ q hJ₀ hs)
  have hmaxQ : IsLocalRing.maximalIdeal (A ⧸ I)
      = Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal A) :=
    (IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).symm
  choose a ha using fun i : Fin n => Ideal.Quotient.mk_surjective (z i)
  have hamem : ∀ i, a i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    refine (Ideal.mem_quotient_iff_mem hIle).mp ?_
    rw [← hmaxQ, ha i, ← hzspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  choose rt hrt using fun i : Fin n => IsLocalization.surj (M := q.primeCompl) (a i)
  have hsq : ∀ i : Fin n, (rt i).1 ∈ q := by
    intro i
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff A q (rt i).1 inferInstance).mp ?_
    rw [← hrt i]
    exact Ideal.mul_mem_right _ _ (hamem i)
  refine ⟨J₀.card + n,
    Fin.append
      (fun i : Fin J₀.card => etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
      (fun i : Fin n => (rt i).1), ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      exact hJ₀ _ (J₀.equivFin.symm i).2
    · rw [Fin.append_right]
      exact hsq i
  · intro j hj
    refine ⟨Fin.castAdd n (J₀.equivFin ⟨j, hj⟩), ?_⟩
    rw [Fin.append_left, Equiv.symm_apply_apply]
  · have hxq : ∀ i : Fin (J₀.card + n),
        Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i ∈ q := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]
        exact hJ₀ _ (J₀.equivFin.symm i).2
      · rw [Fin.append_right]
        exact hsq i
    have hTle : Ideal.span (Set.range fun i =>
        algebraMap S A (Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i)) ≤ IsLocalRing.maximalIdeal A := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A q _ inferInstance).mpr (hxq i)
    have hIT : I ≤ Ideal.span (Set.range fun i =>
        algebraMap S A (Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i)) := by
      rw [hIdef, etaleChartCoordIdeal_eq_span_image, Ideal.map_span, Set.image_image]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, hj, rfl⟩
      refine Ideal.subset_span ⟨Fin.castAdd n (J₀.equivFin ⟨j, Finset.mem_coe.mp hj⟩), ?_⟩
      refine congrArg (algebraMap S A) ?_
      rw [Fin.append_left, Equiv.symm_apply_apply]
    refine le_antisymm hTle ?_
    intro y hy
    refine (Ideal.mem_quotient_iff_mem hIT).mp ?_
    have hz : ∀ i : Fin n, z i ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range fun i =>
        algebraMap S A (Fin.append
          (fun i : Fin J₀.card =>
            etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
          (fun i : Fin n => (rt i).1) i))) := by
      intro i
      have hunit : IsUnit (Ideal.Quotient.mk I (algebraMap S A ((rt i).2 : S))) :=
        (IsLocalization.map_units A ((rt i).2)).map (Ideal.Quotient.mk I)
      obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hunit
      have hmem : Ideal.Quotient.mk I (algebraMap S A ((rt i).1))
          ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range fun i =>
            algebraMap S A (Fin.append
              (fun i : Fin J₀.card =>
                etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
              (fun i : Fin n => (rt i).1) i))) := by
        refine Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨Fin.natAdd J₀.card i, ?_⟩)
        exact congrArg (algebraMap S A) (Fin.append_right _ _ i)
      have heq : Ideal.Quotient.mk I (algebraMap S A ((rt i).1))
          = z i * Ideal.Quotient.mk I (algebraMap S A ((rt i).2 : S)) := by
        rw [← hrt i, map_mul, ha i]
      have hzi : z i = Ideal.Quotient.mk I (algebraMap S A ((rt i).1)) * v := by
        rw [heq, mul_assoc, hv, mul_one]
      rw [hzi]
      exact Ideal.mul_mem_right _ _ hmem
    have hmq : IsLocalRing.maximalIdeal (A ⧸ I) ≤ Ideal.map (Ideal.Quotient.mk I)
        (Ideal.span (Set.range fun i =>
          algebraMap S A (Fin.append
            (fun i : Fin J₀.card =>
              etaleChartCoord k m S ((J₀.equivFin.symm i : {x // x ∈ J₀}) : Fin m))
            (fun i : Fin n => (rt i).1) i))) := by
      rw [← hzspan]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hz i
    refine hmq ?_
    rw [hmaxQ]
    exact Ideal.mem_map_of_mem _ hy
  · have h2 := ringKrullDim_quotient_map_etaleChartCoordIdeal_add_card k m S q A J₀ hJ₀
    rw [← hIdef] at h2
    rw [← h2, ← hzdim, Nat.cast_add]
    exact add_comm _ _
end FunctorialResolution.EmbeddedResolution
