-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ringKrullDim_eq_of_flat_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:09.571121+00:00
-- url     : https://prove2.me/submissions/374f69f8-e1ca-4457-9c5a-308716a92e33

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_prime_le_under_eq_of_hasGoingDown (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S] (p : Ideal R) [p.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hle : p ≤ Ideal.under R Q) :
    ∃ P : Ideal S, P ≤ Q ∧ P.IsPrime ∧ Ideal.under R P = p := by
  rcases eq_or_lt_of_le hle with h | h
  · exact ⟨Q, le_rfl, ‹Q.IsPrime›, h.symm⟩
  · obtain ⟨P, hPQ, hP, hlo⟩ :=
      Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (R := R) Q h
    exact ⟨P, hPQ, hP, hlo.over.symm⟩
private theorem exists_ltSeries_le_of_hasGoingDown (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S] (n : ℕ) :
    ∀ (p : LTSeries (PrimeSpectrum R)), p.length = n →
      ∀ (Q : Ideal S), Q.IsPrime → p.last.asIdeal ≤ Ideal.under R Q →
        ∃ q : LTSeries (PrimeSpectrum S), q.length = n ∧ q.last.asIdeal ≤ Q ∧
          Ideal.under R q.last.asIdeal = p.last.asIdeal := by
  induction n with
  | zero =>
      intro p hp Q hQ hle
      have := hQ
      have : p.last.asIdeal.IsPrime := p.last.isPrime
      obtain ⟨P, hPQ, hP, hunder⟩ := exists_prime_le_under_eq_of_hasGoingDown R S p.last.asIdeal Q hle
      exact ⟨RelSeries.singleton _ ⟨P, hP⟩, rfl, hPQ, hunder⟩
  | succ n ih =>
      intro p hp Q hQ hle
      have := hQ
      have : p.last.asIdeal.IsPrime := p.last.isPrime
      obtain ⟨P, hPQ, hP, hunder⟩ := exists_prime_le_under_eq_of_hasGoingDown R S p.last.asIdeal Q hle
      have hlen : p.length ≠ 0 := by omega
      have hlt : p.eraseLast.last < p.last := p.eraseLast_last_rel_last hlen
      have hltI : p.eraseLast.last.asIdeal < p.last.asIdeal :=
        (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt
      have hlen' : p.eraseLast.length = n := by
        have := RelSeries.eraseLast_length p
        omega
      have hle' : p.eraseLast.last.asIdeal ≤ Ideal.under R P := by
        rw [hunder]
        exact le_of_lt hltI
      obtain ⟨q, hq1, hq2, hq3⟩ := ih p.eraseLast hlen' P hP hle'
      have hne : q.last.asIdeal ≠ P := by
        intro h
        rw [h, hunder] at hq3
        exact (ne_of_lt hltI) hq3.symm
      have hrel : q.last < (⟨P, hP⟩ : PrimeSpectrum S) :=
        (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp (lt_of_le_of_ne hq2 hne)
      refine ⟨q.snoc ⟨P, hP⟩ hrel, ?_, ?_, ?_⟩
      · rw [RelSeries.snoc_length, hq1]
      · rw [RelSeries.last_snoc]; exact hPQ
      · rw [RelSeries.last_snoc]; exact hunder
private theorem ringKrullDim_le_of_hasGoingDown (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.HasGoingDown R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  have key : ∀ p : LTSeries (PrimeSpectrum R), (p.length : WithBot ℕ∞) ≤ ringKrullDim S := by
    intro p
    have hmax : p.last.asIdeal ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal p.last.isPrime.ne_top
    have hp : p.last.asIdeal ≤ Ideal.under R (IsLocalRing.maximalIdeal S) := by
      intro x hx
      exact map_nonunit (algebraMap R S) x (hmax hx)
    obtain ⟨q, hq1, -, -⟩ :=
      exists_ltSeries_le_of_hasGoingDown R S p.length p rfl (IsLocalRing.maximalIdeal S)
        inferInstance hp
    calc (p.length : WithBot ℕ∞) = (q.length : WithBot ℕ∞) := by rw [hq1]
      _ ≤ ringKrullDim S := Order.LTSeries.length_le_krullDim q
  exact iSup_le key
private theorem spanFinrank_map_le (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] (I : Ideal R) :
    (Ideal.map (algebraMap R S) I).spanFinrank ≤ I.spanFinrank := by
  obtain ⟨s, hcard, hspan⟩ := Submodule.exists_span_set_card_eq_spanRank I
  have hIfg : Submodule.FG (I : Submodule R R) := IsNoetherian.noetherian I
  have hrank : I.spanRank = (I.spanFinrank : Cardinal) :=
    Submodule.FG.spanRank_eq_spanFinrank hIfg
  have hslt : Cardinal.mk s < Cardinal.aleph0 := by
    rw [hcard, hrank]
    exact Cardinal.natCast_lt_aleph0
  have hspan' : Ideal.span s = I := hspan
  have hmapspan : Ideal.map (algebraMap R S) I = Ideal.span ((algebraMap R S) '' s) := by
    rw [← hspan', Ideal.map_span]
  have h1 : (Ideal.map (algebraMap R S) I).spanRank ≤ Cardinal.mk ((algebraMap R S) '' s) := by
    rw [hmapspan]
    exact Submodule.spanRank_span_le_card _
  have h2 := Cardinal.mk_image_le_lift (f := (algebraMap R S : R → S)) (s := s)
  have hliftlt : Cardinal.lift.{_, _} (Cardinal.mk s) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mpr hslt
  have h4 : Cardinal.mk ((algebraMap R S) '' s) < Cardinal.aleph0 :=
    Cardinal.lift_lt_aleph0.mp (lt_of_le_of_lt h2 hliftlt)
  have h3 : Cardinal.toNat (Cardinal.mk ((algebraMap R S) '' s)) ≤
      Cardinal.toNat (Cardinal.mk s) := by
    have := Cardinal.toNat_le_toNat h2 hliftlt
    rwa [Cardinal.toNat_lift, Cardinal.toNat_lift] at this
  calc (Ideal.map (algebraMap R S) I).spanFinrank
      = Cardinal.toNat (Ideal.map (algebraMap R S) I).spanRank :=
        Submodule.spanFinrank.eq_def _
    _ ≤ Cardinal.toNat (Cardinal.mk ((algebraMap R S) '' s)) := Cardinal.toNat_le_toNat h1 h4
    _ ≤ Cardinal.toNat (Cardinal.mk s) := h3
    _ = I.spanFinrank := by rw [hcard, ← Submodule.spanFinrank.eq_def]
private theorem ringKrullDim_le_of_map_maximalIdeal (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [_root_.IsRegularLocalRing R] [Algebra R S]
    (hmax : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :
    ringKrullDim S ≤ ringKrullDim R := by
  have : IsNoetherianRing R := inferInstance
  have hne : IsLocalRing.maximalIdeal S ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hh : (IsLocalRing.maximalIdeal S).height ≤ ((IsLocalRing.maximalIdeal S).spanFinrank : ℕ∞) :=
    Ideal.height_le_spanFinrank _ hne
  have hfr : (IsLocalRing.maximalIdeal S).spanFinrank ≤
      (IsLocalRing.maximalIdeal R).spanFinrank := by
    rw [hmax]
    exact spanFinrank_map_le R S _
  have hR := (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := R))
  rw [← hR, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S)]
  have h : (IsLocalRing.maximalIdeal S).height ≤ ((IsLocalRing.maximalIdeal R).spanFinrank : ℕ∞) :=
    le_trans hh (Nat.cast_le.mpr hfr)
  exact_mod_cast h
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [_root_.IsRegularLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    [Module.Flat R S] :
    ringKrullDim S = ringKrullDim R := by
  have : IsLocalRing R := inferInstance
  have : IsNoetherianRing R := inferInstance
  have : Algebra.HasGoingDown R S := inferInstance
  have h1 : ringKrullDim R ≤ ringKrullDim S := ringKrullDim_le_of_hasGoingDown R S
  have hmax : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (algebraMap R S) :=
    (Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)).symm
  exact le_antisymm (ringKrullDim_le_of_map_maximalIdeal R S hmax) h1
end FunctorialResolution.EmbeddedResolution
