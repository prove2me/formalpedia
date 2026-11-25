-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.field_frob_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:51.203478+00:00
-- url     : https://prove2.me/submissions/ec338753-539f-4053-b67a-1a3d7acb37dd

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_galois_map_mul_inv
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_field_inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Frob_frob_mul_inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDecomp
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFrob_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostInertia
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
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ₀ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (h₀ : IsArithFrobAt ℤ σ₀ P)
    (h1 : galoisToProduct e (galE e ζ a b σ₀) - (hostData e q d).frob p ∈ (hostData e q d).inertia p)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    IsArithFrobAt ℤ σ P ↔
      galoisToProduct e (galE e ζ a b σ) - (hostData e q d).frob p ∈ (hostData e q d).inertia p := by
  constructor
  · intro hσ
    have h2 : ∀ x : 𝓞 (hostE ζ a b), (σ * σ₀⁻¹) • x - x ∈ P :=
      AddSubgroup.mem_inertia.mp (hσ.mul_inv_mem_inertia h₀)
    rw [field_inertia h hL p P, galois_map_mul_inv h hL] at h2
    have := AddSubgroup.add_mem _ h2 h1
    rwa [sub_add_sub_cancel] at this
  · intro hσ
    have h2 := AddSubgroup.sub_mem _ hσ h1
    rw [sub_sub_sub_cancel_right, ← galois_map_mul_inv h hL, ← field_inertia h hL p P] at h2
    have := FrobeniusOrbits.Frob.frob_mul_inertia P (σ * σ₀⁻¹) σ₀ (AddSubgroup.mem_inertia.mpr h2) h₀
    rwa [inv_mul_cancel_right] at this
end Formalism.LFunctionChainParameters.LHost
