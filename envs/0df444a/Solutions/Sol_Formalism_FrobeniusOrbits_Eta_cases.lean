-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Eta.cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:21:01.100168+00:00
-- url     : https://prove2.me/submissions/f329e215-d7d1-445e-be8f-db5399813d96

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_NcardEqTwoIff

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
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Eta
variable (K : Type) [Field K] [NumberField K] [IsCMField K]
local notation3 "K⁺" => maximalRealSubfield K
namespace Formalism.FrobeniusOrbits.Eta
theorem _root_.solution (g : K ≃ₐ[K⁺] K) : g = 1 ∨ g = IsCMField.complexConj K := by
  classical
  by_contra hne
  push_neg at hne
  have h2 : Nat.card (K ≃ₐ[K⁺] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  haveI : Fintype (K ≃ₐ[K⁺] K) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h2
  have h3 : ({1, IsCMField.complexConj K, g} : Finset (K ≃ₐ[K⁺] K)).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, IsCMField.complexConj K, g,
      (IsCMField.complexConj_ne_one K).symm, hne.1.symm, hne.2.symm, rfl⟩
  have h4 := Finset.card_le_univ ({1, IsCMField.complexConj K, g} : Finset (K ≃ₐ[K⁺] K))
  omega
end Formalism.FrobeniusOrbits.Eta
