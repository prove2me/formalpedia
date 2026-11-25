-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_etaleChartCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:32.527643+00:00
-- url     : https://prove2.me/submissions/479cc363-5306-4d3a-ae8b-0353512fe044

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateQuotient
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorRadical
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRadical_map_span_singleton_prod_etaleChartCoord
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
private theorem isRadical_span_singleton_of_isRadical_map_atPrime {S : Type u} [CommRing S] (a : S)
    (h : ∀ (Q : Ideal S) [Q.IsPrime],
      (Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S))).IsRadical) :
    (Ideal.span ({a} : Set S)).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
  by_contra hxI
  obtain ⟨K, hKmem⟩ : ∃ K : Ideal S, ∀ b : S, b ∈ K ↔ b * x ∈ Ideal.span ({a} : Set S) :=
    ⟨{ carrier := {s : S | s * x ∈ Ideal.span ({a} : Set S)}
       zero_mem' := by
         show (0 : S) * x ∈ Ideal.span ({a} : Set S)
         rw [zero_mul]
         exact Ideal.zero_mem _
       add_mem' := by
         intro b c hb hc
         show (b + c) * x ∈ Ideal.span ({a} : Set S)
         rw [add_mul]
         exact Ideal.add_mem _ hb hc
       smul_mem' := by
         intro c b hb
         show (c • b) * x ∈ Ideal.span ({a} : Set S)
         rw [smul_eq_mul, mul_assoc]
         exact Ideal.mul_mem_left _ c hb },
     fun b => Iff.rfl⟩
  have hKne : K ≠ ⊤ := by
    intro htop
    have h1 : (1 : S) ∈ K := by rw [htop]; exact Submodule.mem_top
    have h2 := (hKmem 1).mp h1
    rw [one_mul] at h2
    exact hxI h2
  obtain ⟨Q, hQmax, hKQ⟩ := Ideal.exists_le_maximal K hKne
  have hQp : Q.IsPrime := hQmax.isPrime
  have hrad := h Q
  have hpow : (algebraMap S (Localization.AtPrime Q) x) ^ n ∈
      Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S)) := by
    rw [← map_pow]
    exact Ideal.mem_map_of_mem _ hn
  have hxmem : algebraMap S (Localization.AtPrime Q) x ∈
      Ideal.map (algebraMap S (Localization.AtPrime Q)) (Ideal.span ({a} : Set S)) :=
    hrad (Ideal.mem_radical_iff.mpr ⟨n, hpow⟩)
  rw [Ideal.map_span, Set.image_singleton] at hxmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxmem
  obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj (M := Q.primeCompl) c
  have key : algebraMap S (Localization.AtPrime Q) (x * (s : S)) =
      algebraMap S (Localization.AtPrime Q) (a * y) := by
    have h1 : algebraMap S (Localization.AtPrime Q) (x * (s : S))
        = (c * algebraMap S (Localization.AtPrime Q) (s : S)) *
            algebraMap S (Localization.AtPrime Q) a := by
      rw [map_mul, ← hc]; ring
    rw [h1, hys, map_mul]; ring
  obtain ⟨dd, hd⟩ := (IsLocalization.eq_iff_exists Q.primeCompl (Localization.AtPrime Q)).mp key
  have hmem0 : ((dd : S) * (s : S)) * x ∈ Ideal.span ({a} : Set S) := by
    have heq : ((dd : S) * (s : S)) * x = (dd : S) * (x * (s : S)) := by ring
    rw [heq, hd]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self a))
  have hmem : ((dd : S) * (s : S)) ∈ K := (hKmem _).mpr hmem0
  have hQmem : ((dd : S) * (s : S)) ∈ Q := hKQ hmem
  rcases hQp.mem_or_mem hQmem with hcase | hcase
  · exact dd.2 hcase
  · exact s.2 hcase
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (T : Finset (Fin m)) :
    (Ideal.span ({∏ j ∈ T, etaleChartCoord k m S j} : Set S)).IsRadical := by
  refine isRadical_span_singleton_of_isRadical_map_atPrime (∏ j ∈ T, etaleChartCoord k m S j) ?_
  intro Q hQ
  have : Q.IsPrime := hQ
  exact isRadical_map_span_singleton_prod_etaleChartCoord k m S Q (Localization.AtPrime Q) T
end FunctorialResolution.EmbeddedResolution
