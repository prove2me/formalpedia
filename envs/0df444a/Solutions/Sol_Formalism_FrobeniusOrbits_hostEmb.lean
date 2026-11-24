-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:01:21.187818+00:00
-- url     : https://prove2.me/submissions/1745763f-c4e6-4fa8-9857-757c15e8b890

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_isGalois_hostE
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_inj


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
open Formalism.TwoAdicCyclotomicDecomposition
open Misc Galois
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostEmb := by
  intro e q d hqd L _ _ ζ a b hL φ₀
  haveI := Galois.isGalois_hostE hqd hL
  have inj : Function.Injective
      (fun σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b => φ₀.comp (σ : hostE ζ a b →+* hostE ζ a b)) := by
    intro σ τ h
    ext x
    exact congrArg Subtype.val (φ₀.injective (RingHom.congr_fun h x))
  refine inj.bijective_of_nat_card_le ?_
  rw [Nat.card_eq_fintype_card, NumberField.Embeddings.card, IsGalois.card_aut_eq_finrank]
end Formalism.FrobeniusOrbits
