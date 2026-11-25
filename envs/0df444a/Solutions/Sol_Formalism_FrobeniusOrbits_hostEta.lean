-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostEta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:24:49.480033+00:00
-- url     : https://prove2.me/submissions/4555dcd6-7503-408f-80f6-343b5da6c8d3

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_NcardEqTwoIff
import Theorems.Thm_Formalism_FrobeniusOrbits_Eta_split_or_inert
import Theorems.Thm_Formalism_FrobeniusOrbits_Eta_ncard_eq_two_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Eta_galE_cQ
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_eq_inertia_mul
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDecompConj
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFrob_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostUnramEF
import Theorems.Thm_Formalism_FrobeniusOrbits_isCMField_hostE
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Eta
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostEta := by
  intro e q d hH L _ _ ζ a b hL
  have hqd : HypOdd q d := hH.toHypOdd
  haveI hCM : IsCMField (hostE ζ a b) := isCMField_hostE hqd hL
  obtain ⟨-, -, hmul, hbij⟩ := hostGalois e q d hqd L ζ a b hL
  have hc := galE_cQ hqd hL
  have hunr : ∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 (hostE ζ a b), IsCMField.complexConj (hostE ζ a b) • x - x ∈ P :=
    fun P hP hP0 hx => hostUnramEF e q d hH L ζ a b hL P hP hP0 (cQ hqd hL) hc (fun x => hx x)
  have hstab : ∀ P : Ideal (𝓞 (hostE ζ a b)),
      cQ hqd hL ∈ MulAction.stabilizer _ P ↔ IsCMField.complexConj (hostE ζ a b) • P = P :=
    fun P => MulAction.mem_stabilizer_iff
  have hbot : ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (hostE ζ a b)))
      [P.LiesOver (span {(p : ℤ)})], P ≠ ⊥ := by
    intro p hp P _
    have hne : span {(p : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.out.ne_zero
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hne P
  refine ⟨fun 𝔭 h𝔭 h0 => ?_, ?_, ?_⟩
  · haveI := h𝔭
    exact Eta.split_or_inert (hostE ζ a b) hunr 𝔭 h0
  · intro p _ hp2 hpq hpd P _ _ σ hσ
    have hF := hostFrob_of hostGalois hostGalSpec e q d hqd L ζ a b hL p hp2 hpq hpd P
    have key := Eta.ncard_eq_two_iff (hostE ζ a b) hunr P (hbot p P)
    have hM : ∀ (τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (k : ℕ),
        galE e ζ a b (τ ^ k) = galE e ζ a b τ ^ k :=
      fun τ k => map_pow (MonoidHom.mk' (galE e ζ a b) hmul) τ k
    have hE : etaF ζ a b (P.comap (algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)))) = -1 ↔
        cQ hqd hL ∈ MulAction.stabilizer _ P := by
      rw [hstab]
      unfold etaF
      split_ifs with h2
      · constructor
        · intro h; exact absurd h (by norm_num)
        · intro h; exact absurd h (key.mp h2)
      · constructor
        · intro _
          by_contra hne
          exact h2 (key.mpr hne)
        · intro _; rfl
    rw [hE]
    constructor
    · intro hs
      obtain ⟨k, ρ, hρ, hck⟩ := Decomp.stab_eq_inertia_mul p P σ (cQ hqd hL) hσ hs
      have hρ1 : ρ = 1 := (hF.2.2 ρ).mp hρ
      rw [hρ1, one_mul] at hck
      have hk : galE e ζ a b σ ^ k = cc e := by rw [← hM, ← hck, hc]
      generalize galE e ζ a b σ = g at hk ⊢
      obtain ⟨⟨s1, s2⟩, h⟩ := g
      have e1 : s1 ^ k = -1 := by simpa [cc, c0] using congrArg (fun x : GG e => x.1.1) hk
      have e2 : s2 ^ k = -1 := by simpa [cc, c0] using congrArg (fun x : GG e => x.1.2) hk
      have e3 : h ^ k = 1 := by simpa [cc, c0] using congrArg (fun x : GG e => x.2) hk
      have hs : ∀ s : ℤˣ, s ^ k = -1 → s = -1 := by
        intro s hsk
        rcases Int.units_eq_one_or s with rfl | rfl
        · exfalso
          have := congrArg (fun u : ℤˣ => (u : ℤ)) hsk
          simp at this
        · rfl
      have hs1 := hs s1 e1
      have hs2 := hs s2 e2
      have hodd : ¬ 2 ∣ k := by
        rintro ⟨m, rfl⟩
        rw [hs1, pow_mul] at e1
        have := congrArg (fun u : ℤˣ => (u : ℤ)) e1
        simp at this
      have hcardU : Nat.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
          Nat.totient_prime_pow Nat.prime_two (by omega)]
        simp
      have hdvd : orderOf h ∣ 2 ^ (e + 1) := by
        rw [← hcardU]
        exact (orderOf_dvd_natCard h).trans (Subgroup.index_dvd_card _)
      obtain ⟨j, -, hoj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hok : orderOf h ∣ k := orderOf_dvd_of_pow_eq_one e3
      have hj0 : j = 0 := by
        by_contra hj0
        apply hodd
        rw [hoj] at hok
        exact (dvd_pow_self 2 hj0).trans hok
      have hh1 : h = 1 := by
        rw [hj0, pow_zero] at hoj
        exact orderOf_eq_one_iff.mp hoj
      rw [hs1, hs2, hh1]
      rfl
    · intro hg
      have hσc : σ = cQ hqd hL := hbij.1 (hg.trans hc.symm)
      rw [← hσc]
      exact hσ.mem_stabilizer
  · intro p _ hp P _ _
    have key := Eta.ncard_eq_two_iff (hostE ζ a b) hunr P (hbot p P)
    have hnot := hostDecompConj e q d hH L ζ a b hL (cQ hqd hL) hc p hp P
    have h2 := key.mpr (fun h => hnot ((hstab P).mpr h))
    unfold etaF
    split_ifs with h3
    · rfl
    · exact absurd h2 h3
end Formalism.FrobeniusOrbits
