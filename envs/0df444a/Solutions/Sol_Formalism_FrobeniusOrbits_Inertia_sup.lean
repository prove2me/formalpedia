-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Inertia.sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:22:52.357043+00:00
-- url     : https://prove2.me/submissions/095a312a-e2ed-43cb-9c8c-d3ae9c39029d

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_mem_of_restrict
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galE_lift
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_zeta_inversion
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFixed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Inertia
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (g : GalL (e + 2))
    (hg : galE e ζ a b σ = ((g.2.1, g.2.2), hcl e g.1))
    (hI : ∀ τ : Gal(L/ℚ), galMap h.1 a b τ = g → ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime]
      [Q.LiesOver (span {(p : ℤ)})], ∀ y : 𝓞 L, τ • y - y ∈ Q) :
    ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P := by
  haveI := (layer_galois hqd h).1
  have hinj : Function.Injective (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L)) := by
    intro x y hxy
    have h1 := congrArg (fun z : 𝓞 L => (z : L)) hxy
    apply NumberField.RingOfIntegers.ext
    apply Subtype.ext
    exact h1
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 L))
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  haveI := hQp
  haveI : Q.LiesOver P := ⟨hQc.symm⟩
  haveI : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  set τ1 : Gal(L/ℚ) := σ.liftNormal L with hτ1
  have hστ1 : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ1 x :=
    fun x => (σ.liftNormal_commutes L x).symm
  have h1 := galE_lift h hστ1
  rw [hg] at h1
  have hs1 : g.2.1 = (galMap h.1 a b τ1).2.1 := congrArg (fun z : GG e => z.1.1) h1
  have hs2 : g.2.2 = (galMap h.1 a b τ1).2.2 := congrArg (fun z : GG e => z.1.2) h1
  have hh : hcl e g.1 = hcl e (galMap h.1 a b τ1).1 := congrArg Prod.snd h1
  have hpm : g.1 = (galMap h.1 a b τ1).1 ∨ g.1 = -(galMap h.1 a b τ1).1 := by
    unfold hcl at hh
    rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hh
    obtain ⟨k, hk⟩ := hh
    rcases Int.even_or_odd k with hk2 | hk2
    · left
      rw [hk2.neg_one_zpow] at hk
      exact inv_mul_eq_one.1 hk.symm
    · right
      rw [hk2.neg_one_zpow] at hk
      have h3 : (galMap h.1 a b τ1).1 = g.1 * -1 := by rw [hk, mul_inv_cancel_left]
      rw [h3, mul_neg_one, neg_neg]
  obtain ⟨τ, hτg, hστ⟩ : ∃ τ : Gal(L/ℚ), galMap h.1 a b τ = g ∧
      ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x := by
    rcases hpm with hpm | hpm
    · exact ⟨τ1, Prod.ext hpm.symm (Prod.ext hs1.symm hs2.symm), hστ1⟩
    · refine ⟨τ1 * tau0 hqd h, ?_, ?_⟩
      · rw [(layer_galois hqd h).2.2.1, galMap_zeta_inversion]
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · simp [hpm]
        · simp [hs1]
        · simp [hs2]
      · intro x
        rw [hστ1 x, AlgEquiv.mul_apply]
        congr 1
        exact (((hostFixed e q d hqd L ζ a b h).2 x).1 x.2 _ (galMap_zeta_inversion hqd h)).symm
  exact mem_of_restrict P Q σ τ hστ (fun y => hI τ hτg Q y)
end Formalism.FrobeniusOrbits.Inertia
