-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Decomp.stab_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:59:00.960798+00:00
-- url     : https://prove2.me/submissions/66927f33-5364-4813-9912-99ec5e1f99e2

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_mem_stab_of
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_smul_mem_iff_of_stab
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
theorem _root_.solution (P : Ideal (𝓞 (hostE ζ a b))) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x)
    (hτ : τ ∈ MulAction.stabilizer Gal(L/ℚ) Q) :
    σ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P := by
  apply mem_stab_of
  intro z
  rw [mem_P_iff P Q, mem_P_iff P Q, restrict_smul σ τ hστ, smul_mem_iff_of_stab τ Q hτ]
end Formalism.FrobeniusOrbits.Decomp
