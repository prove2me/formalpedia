-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.linearIndependent_toCotangent_etaleChartCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:48:04.251922+00:00
-- url     : https://prove2.me/submissions/24a2ceff-4ccf-4106-84b4-446a3189f10f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoord_injective
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_regularSystemOfParameters_containing_etaleChartCoords
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_of_isLocalization_etale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, etaleChartCoord k m S j ∈ q)
    (hJA : ∀ j ∈ J, algebraMap S A (etaleChartCoord k m S j) ∈ IsLocalRing.maximalIdeal A) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun j : { x : Fin m // x ∈ J } =>
          (IsLocalRing.maximalIdeal A).toCotangent
            ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ :
        { x : Fin m // x ∈ J } → IsLocalRing.CotangentSpace A) := by
  classical
  have hreg : IsRegularLocalRing A := isRegularLocalRing_of_isLocalization_etale k m S q A
  have hnt : Nontrivial S := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · exfalso
      have := hs
      have h10 : (1 : S) = (0 : S) := Subsingleton.elim _ _
      have hA : (1 : A) = 0 := by
        calc (1 : A) = algebraMap S A 1 := (map_one _).symm
          _ = algebraMap S A 0 := by rw [h10]
          _ = 0 := map_zero _
      exact one_ne_zero hA
    · exact hs
  obtain ⟨d, w, hwq, hwJ, hspan, hdim⟩ :=
    exists_regularSystemOfParameters_containing_etaleChartCoords k m S q A J hJ
  have hwm : ∀ i, algebraMap S A (w i) ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin d → IsLocalRing.CotangentSpace A,
      ∀ i, y i = (IsLocalRing.maximalIdeal A).toCotangent ⟨algebraMap S A (w i), hwm i⟩ :=
    ⟨_, fun i => rfl⟩
  have key : ∀ (b : A), b ∈ Ideal.span (Set.range fun i => algebraMap S A (w i)) →
      ∀ (hb : b ∈ IsLocalRing.maximalIdeal A),
        (IsLocalRing.maximalIdeal A).toCotangent ⟨b, hb⟩ ∈
          Submodule.span (IsLocalRing.ResidueField A) (Set.range y) := by
    intro b hb0
    have hb' : b ∈ Submodule.span A (Set.range fun i => algebraMap S A (w i)) := hb0
    clear hb0
    induction hb' using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        intro hz'
        exact Submodule.subset_span ⟨i, by rw [hy i]⟩
    | zero =>
        intro hz'
        have h0 : (⟨(0 : A), hz'⟩ : IsLocalRing.maximalIdeal A) = 0 := rfl
        rw [h0, map_zero]
        exact Submodule.zero_mem _
    | add z z' hz hz' ihz ihz' =>
        intro hbb
        have hzm : z ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz
        have hzm' : z' ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz'
        have hsum : (⟨z + z', hbb⟩ : IsLocalRing.maximalIdeal A) = ⟨z, hzm⟩ + ⟨z', hzm'⟩ := rfl
        rw [hsum, map_add]
        exact Submodule.add_mem _ (ihz hzm) (ihz' hzm')
    | smul c z hz ih =>
        intro hbb
        have hzm : z ∈ IsLocalRing.maximalIdeal A := by rw [← hspan]; exact hz
        have hsm : (⟨c • z, hbb⟩ : IsLocalRing.maximalIdeal A) = c • ⟨z, hzm⟩ := rfl
        rw [hsm, map_smul, ← IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField A) c]
        exact Submodule.smul_mem _ _ (ih hzm)
  have hspanY : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField A) (Set.range y) := by
    intro v _
    obtain ⟨⟨b, hb⟩, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal A) v
    exact key b (by rw [hspan]; exact hb) hb
  have hcard0 : ((d : ℕ) : WithBot ℕ∞) =
      ((Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) : ℕ) :
        WithBot ℕ∞) :=
    hdim.trans ((IsRegularLocalRing.iff_finrank_cotangentSpace A).mp ‹_›).symm
  have hcard : Fintype.card (Fin d) =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) := by
    rw [Fintype.card_fin]
    exact_mod_cast hcard0
  have hliY : LinearIndependent (IsLocalRing.ResidueField A) y :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanY hcard
  have hchoice : ∀ j : { x : Fin m // x ∈ J },
      ∃ i : Fin d, w i = etaleChartCoord k m S (j : Fin m) := fun j => hwJ (j : Fin m) j.2
  choose f hf using hchoice
  have hfinj : Function.Injective f := by
    intro j₁ j₂ hjj
    have h1 : etaleChartCoord k m S (j₁ : Fin m) = etaleChartCoord k m S (j₂ : Fin m) := by
      rw [← hf j₁, ← hf j₂, hjj]
    exact Subtype.ext (etaleChartCoord_injective k m S h1)
  have hcomp := hliY.comp f hfinj
  have heq : y ∘ f = fun j : { x : Fin m // x ∈ J } =>
      (IsLocalRing.maximalIdeal A).toCotangent
        ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ := by
    funext j
    have h1 : (⟨algebraMap S A (w (f j)), hwm (f j)⟩ : IsLocalRing.maximalIdeal A)
        = ⟨algebraMap S A (etaleChartCoord k m S (j : Fin m)), hJA (j : Fin m) j.2⟩ :=
      Subtype.ext (congrArg (algebraMap S A) (hf j))
    show y (f j) = _
    rw [hy (f j)]
    exact congrArg _ h1
  rw [← heq]
  exact hcomp
end FunctorialResolution.EmbeddedResolution
