-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.galE_mem_Psi_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:26:15.538501+00:00
-- url     : https://prove2.me/submissions/f727d52f-cb95-4d59-93c1-920c346d0ecd

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
section Hcl
variable {e : ℕ}
end Hcl
section Subfields
variable {L : Type*} [Field L] [Algebra ℚ L] {ζ a b : L}
end Subfields
section Signs
variable {e : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {ζ a b : L}
private lemma sgn_eq_one_iff_apply_eq {M : Type*} [Field M] [Algebra ℚ M] (σ : M ≃ₐ[ℚ] M) (x : M) :
    Formalism.TwoAdicCyclotomicDecomposition.sgn σ x = 1 ↔ σ x = x := by
  unfold Formalism.TwoAdicCyclotomicDecomposition.sgn
  by_cases hx : σ x = x
  · rw [if_pos hx]
    exact iff_of_true rfl hx
  · rw [if_neg hx]
    exact iff_of_false (by decide) hx
end Signs
section Layer
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
end Layer
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
variable {e : ℕ} {L : Type*} [Field L] [Algebra ℚ L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    galE e ζ a b σ ∈ Psi e ↔ σ (bE ζ a b) = bE ζ a b := by
  unfold galE Psi
  rw [MonoidHom.mem_ker]
  exact sgn_eq_one_iff_apply_eq σ (bE ζ a b)
end Formalism.FrobeniusOrbits
