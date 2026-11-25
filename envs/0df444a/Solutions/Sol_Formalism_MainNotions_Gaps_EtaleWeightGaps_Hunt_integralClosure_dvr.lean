-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt.integralClosure_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:34.27526+00:00
-- url     : https://prove2.me/submissions/8aa6118a-35f5-47d5-8ac8-92f36cb58b89

import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_IsIntegralOfAll
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Hunt_isIntegral_of_all
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_isDVRAt_of_field_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
theorem _root_.solution :
    ∀ (O K A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [CharZero K] [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A]
    [FiniteDimensional K A] [IsReduced A],
    Module.Finite O ↥(As O A) ∧ ∀ ζ : Pts O A, IsDVRAt ζ := by
  intro O K A _ _ _ _ _ _ _ _ _ _ _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI := Fintype.ofFinite (MaximalSpectrum A)
  have hinj : ∀ a : A, (∀ m : MaximalSpectrum A, Ideal.Quotient.mk m.asIdeal a = 0) → a = 0 := fun a h => by
    apply (IsArtinianRing.equivPi A).injective
    rw [map_zero]
    funext m
    exact h m
  have hsurj : ∀ b : (m : MaximalSpectrum A) → A ⧸ m.asIdeal, ∃ a : A, ∀ m, Ideal.Quotient.mk m.asIdeal a = b m := fun b => by
    obtain ⟨a, ha⟩ := (IsArtinianRing.equivPi A).surjective b
    exact ⟨a, fun m => congrFun ha m⟩
  constructor
  · haveI : ∀ m : MaximalSpectrum A, Module.Finite O ↥(As O (A ⧸ m.asIdeal)) := fun m => by
      haveI := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      exact IsIntegralClosure.finite O K (A ⧸ m.asIdeal) _
    refine Module.Finite.of_injective (LinearMap.pi fun m : MaximalSpectrum A => (redAs O A m.asIdeal).toLinearMap) ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    apply Subtype.ext
    exact hinj _ fun m => congrArg Subtype.val (congrFun ha m)
  · intro ζ
    choose e he using fun m : MaximalSpectrum A => hsurj (Pi.single m 1)
    have hei : ∀ m, IsIntegral O (e m) := fun m => isIntegral_of_all O A _ fun m' => by
      rw [he]
      by_cases h : m' = m
      · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
      · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
    have hsum : ∑ m, (⟨e m, hei m⟩ : ↥(As O A)) = 1 := by
      apply Subtype.ext
      rw [← sub_eq_zero]
      apply hinj
      intro m'
      rw [map_sub]
      simp only [AddSubmonoidClass.coe_finsetSum, map_sum, he, OneMemClass.coe_one, map_one]
      rw [← Finset.sum_apply, Finset.univ_sum_single]
      simp
    obtain ⟨m, hm⟩ : ∃ m, (⟨e m, hei m⟩ : ↥(As O A)) ∉ ζ.asIdeal := by
      by_contra hc
      push Not at hc
      exact ζ.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 (hsum ▸ Ideal.sum_mem _ fun m _ => hc m))
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    let f := redAs O A m.asIdeal
    have hf : Function.Surjective f := fun b => by
      obtain ⟨a, ha⟩ := hsurj (Pi.single m (b : A ⧸ m.asIdeal))
      refine ⟨⟨a, isIntegral_of_all O A _ fun m' => ?_⟩, Subtype.ext ?_⟩
      · rw [ha]
        by_cases h : m' = m
        · subst h; rw [Pi.single_eq_same]; exact b.2
        · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
      · show Ideal.Quotient.mk m.asIdeal a = _
        rw [ha, Pi.single_eq_same]
    have hker : ∀ x, f x = 0 → (⟨e m, hei m⟩ : ↥(As O A)) * x = 0 := fun x hx => by
      apply Subtype.ext
      apply hinj
      intro m'
      show Ideal.Quotient.mk m'.asIdeal (e m * x) = 0
      rw [map_mul, he]
      by_cases h : m' = m
      · subst h
        have : Ideal.Quotient.mk m'.asIdeal (x : A) = 0 := congrArg Subtype.val hx
        rw [this, mul_zero]
      · rw [Pi.single_eq_of_ne h, zero_mul]
    have hkl : RingHom.ker f.toRingHom ≤ ζ.asIdeal := fun x hx =>
      (ζ.isMaximal.isPrime.mem_or_mem (by rw [hker x hx]; exact zero_mem _)).resolve_left hm
    have hcm : (ζ.asIdeal.map f.toRingHom).comap f.toRingHom = ζ.asIdeal := by
      rw [Ideal.comap_map_of_surjective f.toRingHom hf]
      exact sup_eq_left.2 hkl
    have hmax : (ζ.asIdeal.map f.toRingHom).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective f.toRingHom hf ζ.isMaximal with h | h
      · rw [h, Ideal.comap_top] at hcm; exact absurd hcm.symm ζ.isMaximal.ne_top
      · exact h
    let ζ' : Pts O (A ⧸ m.asIdeal) := ⟨ζ.asIdeal.map f.toRingHom, hmax⟩
    have hmem : ∀ x, f x ∈ ζ'.asIdeal ↔ x ∈ ζ.asIdeal := fun x => by
      rw [← hcm]; exact Iff.rfl
    have hD : IsDVRAt ζ' := isDVRAt_of_field_ext K ζ'
    letI alg : Algebra ↥(As O A) (Loc ζ') := ((algebraMap _ (Loc ζ')).comp f.toRingHom).toAlgebra
    have halg : ∀ x, algebraMap ↥(As O A) (Loc ζ') x = algebraMap _ (Loc ζ') (f x) := fun _ => rfl
    haveI : IsLocalization.AtPrime (Loc ζ') ζ.asIdeal := by
      refine ⟨⟨fun s => ?_, fun z => ?_, fun {x y} h => ?_⟩⟩
      · rw [halg]
        exact IsLocalization.map_units (Loc ζ') (⟨f s, fun h => s.2 ((hmem _).1 h)⟩ : ζ'.asIdeal.primeCompl)
      · obtain ⟨⟨b, t⟩, hb⟩ := IsLocalization.surj ζ'.asIdeal.primeCompl z
        obtain ⟨a, rfl⟩ := hf b
        obtain ⟨s, hs⟩ := hf t
        refine ⟨⟨a, ⟨s, fun h => t.2 (hs ▸ (hmem _).2 h)⟩⟩, ?_⟩
        simp only [halg, hs]
        exact hb
      · rw [halg, halg] at h
        obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists ζ'.asIdeal.primeCompl (Loc ζ')).1 h
        obtain ⟨s, hs⟩ := hf t
        have hs' : s ∉ ζ.asIdeal := fun h => t.2 (hs ▸ (hmem _).2 h)
        refine ⟨⟨⟨e m, hei m⟩ * s, fun h => (ζ.isMaximal.isPrime.mem_or_mem h).elim hm hs'⟩, ?_⟩
        have := hker (s * x - s * y) (by rw [map_sub, map_mul, map_mul, hs, ht, sub_self])
        show ⟨e m, hei m⟩ * s * x = ⟨e m, hei m⟩ * s * y
        rw [← sub_eq_zero, ← this]; ring
    let E := (IsLocalization.algEquiv ζ.asIdeal.primeCompl (Loc ζ') (Loc ζ)).toRingEquiv
    haveI := hD.isDomain
    haveI := hD.isDVR
    haveI hd : IsDomain (Loc ζ) := E.symm.toMulEquiv.isDomain _
    exact ⟨hd, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E⟩
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
