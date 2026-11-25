-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostDecomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:20.83671+00:00
-- url     : https://prove2.me/submissions/830777dd-17d8-44da-b33e-93f9cbd76573

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_eq_inertia_mul
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_restrict
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_frob_restrict
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_hPart_inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_aE_sq_eq_neg_q
import Theorems.Thm_P2M_Formalism_FrobeniusOrbits_Decomp_bE_sq__6a1d7841da62
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_two_sgn
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_exists_lift
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_exists_restrict
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galE_lift
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypQD
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostRecip
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerDecompTwo
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerInertiaTame
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_cyc_frob
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_frob_sgn
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_mem_Id
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_mem_Iq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_sgn_inertia


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Decomp
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostDecomp := by
  intro e q d hH L _ _ ζ a b h uq ud huq hud σ
  have hqd := hH.toHypOdd
  have hQD := hH.toHypQD
  have hrec := hostRecip q d hH
  obtain ⟨hq, hd, -, hd16, hjac⟩ := hH
  have hq2 : q ≠ 2 := hqd.2.2.2.1
  have hd2 : d ≠ 2 := hqd.2.2.2.2
  have hqd' : q ≠ d := hqd.2.2.1
  obtain ⟨hLgal, -, hmulL, hbijL⟩ := layer_galois hqd h
  have := hLgal
  obtain ⟨hEgal, -, hmulE, hbijE⟩ := hostGalois e q d hqd L ζ a b h
  have := hEgal
  let gE : (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) →* GG e := MonoidHom.mk' (galE e ζ a b) hmulE
  let gL : Gal(L/ℚ) →* GalL (e + 2) := MonoidHom.mk' (galMap h.1 a b) hmulL
  have hpowE : ∀ (x : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (k : ℕ),
      galE e ζ a b (x ^ k) = galE e ζ a b x ^ k := fun x k => map_pow gE x k
  have hpowL : ∀ (x : Gal(L/ℚ)) (k : ℕ), galMap h.1 a b (x ^ k) = galMap h.1 a b x ^ k :=
    fun x k => map_pow gL x k
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [h.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [h.2.2.1]; push_cast; rfl
  have hqnd : ¬ q ∣ d := fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp hdv)
  have hdnq : ¬ d ∣ q := fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hd hq).mp hdv).symm
  have hIT := layerInertiaTame (e + 2) q d (by omega) hqd L ζ a b h
  refine ⟨fun P _ _ => ?_, fun P _ _ => ?_, fun P _ _ => ?_⟩
  ·
    obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
    have : Q.LiesOver (span {(2 : ℤ)}) := Ideal.LiesOver.trans Q P (span {(2 : ℤ)})
    rw [mem_Psi_iff]
    refine ⟨stab_two_sgn hqd hd16 h P σ, fun hs => ?_⟩
    obtain ⟨τ, hστ⟩ := exists_lift hqd h σ
    have hgl := galE_lift h hστ
    apply stab_restrict P Q σ τ hστ
    rw [layerDecompTwo (e + 2) q d (by omega) hQD L ζ a b h Q τ, D2, MonoidHom.mem_ker]
    have h1 := congrArg (fun g : GG e => g.1.2) hgl
    simp only at h1
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_snd]
    rw [← h1]
    exact hs
  ·
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
    have : Q.LiesOver (span {(q : ℤ)}) := Ideal.LiesOver.trans Q P (span {(q : ℤ)})
    have : Finite (𝓞 L ⧸ Q) := by
      have hpb : span {(q : ℤ)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hq.ne_zero
      exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)
    obtain ⟨F, hF⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
    obtain ⟨σF, hσF⟩ := exists_restrict hqd h F
    have hFE : IsArithFrobAt ℤ σF P := frob_restrict q Q P σF F hσF hF
    have hF1 : (galMap h.1 a b F).1 = uq := Units.ext ((odd_cyc_frob h.1 q hq2 Q F hF).trans huq.symm)
    have hF3 : (galMap h.1 a b F).2.2 = 1 := by
      have := odd_frob_sgn q hq2 Q F hF b _ hb
        (by rw [dvd_neg]; intro h'; exact hqnd (by exact_mod_cast h'))
      rw [hjac] at this
      exact Units.ext this
    have hgF : galE e ζ a b σF = (((galMap h.1 a b F).2.1, 1), hcl e uq) := by
      rw [galE_lift h hσF, hF3, hF1]
    constructor
    · intro hσ
      obtain ⟨k, ρ, hρ, rfl⟩ := stab_eq_inertia_mul q P σF σ hFE hσ
      have e2 : (galE e ζ a b ρ).2 = 1 := hPart_inertia hqd h q hq hq2 Q P ρ hρ
      have e1 : (galE e ζ a b ρ).1.2 = 1 :=
        odd_sgn_inertia q hq hq2 P ρ hρ (bE ζ a b) d (bE_sq' h) hqnd
      rw [hmulE, hpowE, hgF]
      refine ⟨?_, k, ?_⟩
      · simp [e1]
      · simp [e2]
    · rintro ⟨hs2, k, hk⟩
      set s' : ℤˣ := (galE e ζ a b σ).1.1 * ((galMap h.1 a b F).2.1 ^ k)⁻¹ with hs'
      obtain ⟨ι, hι⟩ := hbijL.2 ((1, s', 1) : GalL (e + 2))
      have hιI : ∀ x : 𝓞 L, ι • x - x ∈ Q := by
        rw [hIT.1 Q ι, odd_mem_Iq, hι]
        rcases Int.units_eq_one_or s' with hs | hs <;> rw [hs]
        · left; rfl
        · right; rfl
      have hτ : ι * F ^ k ∈ MulAction.stabilizer Gal(L/ℚ) Q :=
        Subgroup.mul_mem _ (Ideal.inertia_le_stabilizer (M := Gal(L/ℚ)) Q
          (AddSubgroup.mem_inertia.mpr hιI)) (Subgroup.pow_mem _ hF.mem_stabilizer k)
      obtain ⟨σ', hσ'⟩ := exists_restrict hqd h (ι * F ^ k)
      have hgm : galMap h.1 a b (ι * F ^ k) =
          ((galMap h.1 a b F).1 ^ k, s' * (galMap h.1 a b F).2.1 ^ k, 1) := by
        rw [hmulL, hpowL, hι]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hF3]
      have hσσ : σ' = σ := by
        apply hbijE.1
        rw [galE_lift h hσ', hgm, hF1]
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · rw [hs', inv_mul_cancel_right]
        · exact hs2.symm
        · rw [hk]; exact QuotientGroup.mk_pow _ uq k
      rw [← hσσ]
      exact stab_restrict P Q σ' _ hσ' hτ
  ·
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
    have : Q.LiesOver (span {(d : ℤ)}) := Ideal.LiesOver.trans Q P (span {(d : ℤ)})
    have : Finite (𝓞 L ⧸ Q) := by
      have hpb : span {(d : ℤ)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hd.ne_zero
      exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)
    obtain ⟨F, hF⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
    obtain ⟨σF, hσF⟩ := exists_restrict hqd h F
    have hFE : IsArithFrobAt ℤ σF P := frob_restrict d Q P σF F hσF hF
    have hF1 : (galMap h.1 a b F).1 = ud := Units.ext ((odd_cyc_frob h.1 d hd2 Q F hF).trans hud.symm)
    have hF2 : (galMap h.1 a b F).2.1 = -1 := by
      have := odd_frob_sgn d hd2 Q F hF a _ ha
        (by rw [dvd_neg]; intro h'; exact hdnq (by exact_mod_cast h'))
      rw [hrec] at this
      exact Units.ext this
    have hgF : galE e ζ a b σF = ((-1, (galMap h.1 a b F).2.2), hcl e ud) := by
      rw [galE_lift h hσF, hF2, hF1]
    constructor
    · intro hσ
      obtain ⟨k, ρ, hρ, rfl⟩ := stab_eq_inertia_mul d P σF σ hFE hσ
      have e2 : (galE e ζ a b ρ).2 = 1 := hPart_inertia hqd h d hd hd2 Q P ρ hρ
      have e1 : (galE e ζ a b ρ).1.1 = 1 :=
        odd_sgn_inertia d hd hd2 P ρ hρ (aE ζ a b) q (aE_sq_eq_neg_q h) hdnq
      rw [hmulE, hpowE, hgF]
      refine ⟨k, ?_, ?_⟩
      · simp [e1]
      · simp [e2]
    · rintro ⟨k, hk1, hk2⟩
      set t' : ℤˣ := (galE e ζ a b σ).1.2 * ((galMap h.1 a b F).2.2 ^ k)⁻¹ with ht'
      obtain ⟨ι, hι⟩ := hbijL.2 ((1, 1, t') : GalL (e + 2))
      have hιI : ∀ x : 𝓞 L, ι • x - x ∈ Q := by
        rw [hIT.2 Q ι, odd_mem_Id, hι]
        rcases Int.units_eq_one_or t' with ht | ht <;> rw [ht]
        · left; rfl
        · right; rfl
      have hτ : ι * F ^ k ∈ MulAction.stabilizer Gal(L/ℚ) Q :=
        Subgroup.mul_mem _ (Ideal.inertia_le_stabilizer (M := Gal(L/ℚ)) Q
          (AddSubgroup.mem_inertia.mpr hιI)) (Subgroup.pow_mem _ hF.mem_stabilizer k)
      obtain ⟨σ', hσ'⟩ := exists_restrict hqd h (ι * F ^ k)
      have hgm : galMap h.1 a b (ι * F ^ k) =
          ((galMap h.1 a b F).1 ^ k, (-1) ^ k, t' * (galMap h.1 a b F).2.2 ^ k) := by
        rw [hmulL, hpowL, hι]
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hF2]
      have hσσ : σ' = σ := by
        apply hbijE.1
        rw [galE_lift h hσ', hgm, hF1]
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · exact hk1.symm
        · rw [ht', inv_mul_cancel_right]
        · rw [hk2]; exact QuotientGroup.mk_pow _ ud k
      rw [← hσσ]
      exact stab_restrict P Q σ' _ hσ' hτ
end Formalism.FrobeniusOrbits
