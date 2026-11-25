-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.field_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:35.247541+00:00
-- url     : https://prove2.me/submissions/37ad8e81-f8a0-4032-92a9-bab7b62d9c06

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_unram
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_two
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_q
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_host_inertia_d
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_coprime_hostN
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_galois_map_one
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_galois_map_injective
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_LHost_galE_one__f70a3826398f
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_galois_map_first_eq_zero_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_galois_map_sign
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_galois_map_complex_conjugation
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
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution (h : HostHyp q d) (hL : IsLayer (e + 2) q d ζ a b) (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [hPl : P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    (∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔ galoisToProduct e (galE e ζ a b σ) ∈ (hostData e q d).inertia p := by
  have hI := hostInertia e q d h L ζ a b hL σ
  have hinj := galois_map_injective e
  by_cases hp2 : p = 2
  · subst hp2
    have : P.LiesOver (span {(2 : ℤ)}) := by simpa using hPl
    rw [hI.1 P, host_inertia_two h, galois_map_first_eq_zero_iff]
  by_cases hpq : p = q
  · subst hpq
    rw [hI.2.1 P, host_inertia_q h, ← galois_map_one e, ← galois_map_sign, hinj.eq_iff, hinj.eq_iff]
  by_cases hpd : p = d
  · subst hpd
    rw [hI.2.2 P, host_inertia_d h, ← galois_map_one e, ← galois_map_complex_conjugation, hinj.eq_iff, hinj.eq_iff]
  have hp : p.Prime := Fact.out
  rw [(hostFrob_of hostGalois hostGalSpec e q d h.toHypOdd L ζ a b hL p hp2 hpq hpd P).2.2 σ,
    (host_unram h p (coprime_hostN e h hp hp2 hpq hpd) hp).1, AddSubgroup.mem_bot, ← galois_map_one e, hinj.eq_iff,
    ← galE_one' h hL, (hostGalois e q d h.toHypOdd L ζ a b hL).2.2.2.1.eq_iff]
end Formalism.LFunctionChainParameters.LHost
