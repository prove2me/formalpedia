-- Prove2me | solution 1 for Formalism.L2.NT.ncard_places_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:01:16.601233+00:00
-- url     : https://prove2.me/submissions/f4305222-7c61-4e99-a592-a9ccd3819870

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
namespace Formalism.L2.NT
theorem _root_.solution {A B : Type} [Field A] [Field B] (e : A ≃+* B) (p : ℕ) :
    ({v : HeightOneSpectrum (𝓞 A) | ((p : ℕ) : 𝓞 A) ∈ v.asIdeal}).ncard =
      ({v : HeightOneSpectrum (𝓞 B) | ((p : ℕ) : 𝓞 B) ∈ v.asIdeal}).ncard := by
  set e' := NumberField.RingOfIntegers.mapRingEquiv e
  have nb : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R ≃+* S) (I : Ideal R), I ≠ ⊥ → I.comap f.symm ≠ ⊥ := by
    intro R S _ _ f I hI h
    apply hI
    have := Ideal.map_comap_of_surjective f.symm f.symm.surjective I
    rw [h, Ideal.map_bot] at this
    exact this.symm
  refine Set.ncard_congr (fun v _ => (⟨v.asIdeal.comap e'.symm, Ideal.comap_isPrime _ _, nb e' _ v.ne_bot⟩ :
    HeightOneSpectrum (𝓞 B))) ?_ ?_ ?_
  · intro v hv
    simp only [Set.mem_ofPred_eq, Ideal.mem_comap, map_natCast] at hv ⊢
    exact hv
  · intro v w _ _ h
    have h' : v.asIdeal.comap e'.symm = w.asIdeal.comap e'.symm := congrArg HeightOneSpectrum.asIdeal h
    exact HeightOneSpectrum.ext (Ideal.comap_injective_of_surjective e'.symm e'.symm.surjective h')
  · intro w hw
    refine ⟨⟨w.asIdeal.comap e'.symm.symm, Ideal.comap_isPrime _ _, nb e'.symm _ w.ne_bot⟩, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Ideal.mem_comap, map_natCast] at hw ⊢
      exact hw
    · apply HeightOneSpectrum.ext
      ext x
      simp only [Ideal.mem_comap, RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
end Formalism.L2.NT
