-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.exists_frob_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:54:24.927137+00:00
-- url     : https://prove2.me/submissions/64a3e664-e41a-4dae-b245-0de12d974cd1

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDecomp
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFrob_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostInertia
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerGalois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card_under
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_cyc_frob
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_frob_sgn
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_intCast_mem_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)
open NumberField Ideal
open Formalism.FrobeniusOrbits (hostE galE aE bE hostGalois hostGalSpec hostInertia hostDecomp hostFrob_of)
open Formalism.TwoAdicCyclotomicDecomposition (IsLayer galMap layerGalois odd_cyc_frob odd_frob_sgn odd_card_under odd_intCast_mem_iff)
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
variable [Fact q.Prime] [Fact d.Prime]
omit [Fact q.Prime] [Fact d.Prime]
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    ∃ σ₀ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, IsArithFrobAt ℤ σ₀ P ∧
      (∀ hp : p.Coprime (2 ^ (e + 2)), (galE e ζ a b σ₀).2 = hcl e (ZMod.unitOfCoprime p hp)) ∧
      (p ≠ q → (((galE e ζ a b σ₀).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p) ∧
      (p ≠ d → (((galE e ζ a b σ₀).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p) := by
  have hqd := h.toHypOdd
  have hp : p.Prime := Fact.out
  obtain ⟨hEgal, -, -, -⟩ := hostGalois e q d hqd L ζ a b hL
  obtain ⟨hLgal, -, -, -⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b hL
  have := hEgal
  have := hLgal
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
  have : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P (span {(p : ℤ)})
  have : Finite (𝓞 L ⧸ Q) := by
    have hpb : span {(p : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    exact Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot hpb Q)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
  let σ₀ : Gal(hostE ζ a b/ℚ) := τ.restrictNormal (hostE ζ a b)
  have hσ₀ : ∀ x : hostE ζ a b, ((σ₀ x : hostE ζ a b) : L) = τ x :=
    fun x => AlgEquiv.restrictNormal_commutes τ (hostE ζ a b) x
  have hσ₀F : IsArithFrobAt ℤ σ₀ P := by
    intro x
    have hx := hτ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x)
    rw [odd_card_under p Q] at hx
    rw [odd_card_under p P]
    rw [Ideal.over_def Q P, Ideal.under_def, Ideal.mem_comap]
    convert hx using 1
    apply RingOfIntegers.coe_injective
    simp only [map_sub, map_pow, MulSemiringAction.toAlgHom_apply]
    congr 1
    show (((σ₀ • x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L) =
      τ (((x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L)
    exact hσ₀ x
  have hval := (hostGalSpec e q d hqd L ζ a b hL σ₀).2.2.2 τ hσ₀
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [hL.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [hL.2.2.1]; push_cast; rfl
  refine ⟨σ₀, hσ₀F, fun hc => ?_, fun hpq => ?_, fun hpd => ?_⟩
  · rw [hval]
    change hcl e (galMap hL.1 a b τ).1 = _
    congr 1
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    exact odd_cyc_frob hL.1 p hp2 Q τ hτ
  · rw [hval]
    refine odd_frob_sgn p hp2 Q τ hτ a _ ha ?_
    rw [dvd_neg]
    intro hd'
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hqd.1).mp (by exact_mod_cast hd'))
  · rw [hval]
    refine odd_frob_sgn p hp2 Q τ hτ b _ hb ?_
    rw [dvd_neg]
    intro hd'
    exact hpd ((Nat.prime_dvd_prime_iff_eq hp hqd.2.1).mp (by exact_mod_cast hd'))
end Formalism.LFunctionChainParameters.LHost
