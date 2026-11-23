-- Prove2me | solution 1 for Formalism.CyclotomicNorms.eigen_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:52.992231+00:00
-- url     : https://prove2.me/submissions/186bb82a-9799-4afb-9d67-3b54a41f0370

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_RestrictionOfBlocksAndJordan
import Theorems.Thm_Formalism_CyclotomicNorms_repr_diag_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open Formalism Formalism.CyclotomicNorms
variable {G k V : Type} [Group G] [Field k] [AddCommGroup V] [Module k V] {N : ℕ}
namespace Formalism.CyclotomicNorms
theorem _root_.solution (ρ : Representation k G V) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → G → k) (I : Subgroup G) (he : ∀ i, ∀ y ∈ I, ρ y (e i) = χ i y • e i)
    (hsep : ∀ i j, i ≠ j → ∃ y ∈ I, χ i y ≠ χ j y)
    (j : Fin N) (v : V) (hv : ∀ y ∈ I, ρ y v = χ j y • v) : v ∈ k ∙ e j := by
  have hc : ∀ i, i ≠ j → e.repr v i = 0 := by
    intro i hij
    obtain ⟨y, hyI, hne⟩ := hsep i j hij
    have h1 := repr_diag_apply ρ e χ y (fun l => he l y hyI) v i
    rw [hv y hyI, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have h2 : (χ j y - χ i y) * e.repr v i = 0 := by rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  rw [Submodule.mem_span_singleton]
  refine ⟨e.repr v j, ?_⟩
  conv_rhs => rw [← e.sum_repr v]
  symm
  exact Finset.sum_eq_single j (fun i _ hij => by rw [hc i hij, zero_smul])
    (fun h => absurd (Finset.mem_univ j) h)
end Formalism.CyclotomicNorms
