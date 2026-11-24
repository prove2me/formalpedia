-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:21:27.993156+00:00
-- url     : https://prove2.me/submissions/56e8034e-b83b-4574-8a3b-ddf7667396ef

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_frob_pow

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
namespace Formalism.FrobeniusOrbits.Decomp
theorem _root_.solution {M : Type} [Field M] [NumberField M] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (F σ : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (hσ : σ ∈ MulAction.stabilizer Gal(M/ℚ) Q) :
    ∃ k : ℕ, ∃ ρ : Gal(M/ℚ), (∀ x : 𝓞 M, ρ • x - x ∈ Q) ∧ σ = ρ * F ^ k := by
  obtain ⟨k, hk⟩ := stab_frob_pow p Q F σ hF hσ
  refine ⟨k, σ * (F ^ k)⁻¹, fun x => ?_, by simp⟩
  have hx := hk ((F ^ k)⁻¹ • x)
  rwa [smul_inv_smul, ← mul_smul] at hx
end Formalism.FrobeniusOrbits.Decomp
