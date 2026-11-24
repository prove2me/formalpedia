-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.conv_char
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.457904+00:00
-- url     : https://prove2.me/submissions/aaf0a04b-8eed-47c2-99b5-f5638284aa81

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_schur_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (a : G → ℂ) (ha : ∀ g k, a (k * g * k⁻¹) = a g) :
    ∃ μ : ℂ, ∀ k, ∑ g, a g * ρ.character (g * k) = μ * ρ.character k := by
  obtain ⟨μ, hμ⟩ := schur_scalar ρ h a ha
  refine ⟨μ, fun k => ?_⟩
  have h2 := congrArg (fun T : Module.End ℂ V => LinearMap.trace ℂ V (T * ρ k)) hμ
  simp only [Finset.sum_mul, smul_mul_assoc, ← map_mul, map_sum, map_smul, one_mul, smul_eq_mul] at h2
  exact h2
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
