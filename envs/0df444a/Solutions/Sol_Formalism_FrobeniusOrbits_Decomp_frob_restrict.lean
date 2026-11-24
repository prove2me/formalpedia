-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Decomp.frob_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:54:04.91187+00:00
-- url     : https://prove2.me/submissions/fa373b4d-9e17-47b4-9a02-57d33ac38401

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_restrict_smul
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_mem_P_iff

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
open Formalism.FrobeniusOrbits.Decomp
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Decomp
theorem _root_.solution (p : ℕ) (Q : Ideal (𝓞 L)) [Q.LiesOver (span {(p : ℤ)})]
    (P : Ideal (𝓞 (hostE ζ a b))) [Q.LiesOver P] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) (hτ : IsArithFrobAt ℤ τ Q) :
    IsArithFrobAt ℤ σ P := by
  have hPQ : P.under ℤ = Q.under ℤ :=
    (Ideal.LiesOver.over : span {(p : ℤ)} = P.under ℤ).symm.trans
      (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ)
  intro x
  have h2 := hτ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x)
  rw [mem_P_iff P Q, map_sub, map_pow, hPQ]
  convert h2 using 2
  exact restrict_smul σ τ hστ x
end Formalism.FrobeniusOrbits.Decomp
