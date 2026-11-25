-- Prove2me | solution 1 for Formalism.L2.N.ExtNRows.finrank_span_image_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:30.324928+00:00
-- url     : https://prove2.me/submissions/0af69714-875e-4878-bf49-a725a7b1fc72

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExtNRowsGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.L2 Formalism.L2.N Formalism.L2.N.ExtNRows
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
namespace Formalism.L2.N.ExtNRows
theorem _root_.solution {n : ℕ} (σ : K →+* ℂ) (j : (Fin n → K) →ₛₗ[σ] W) (A : Submodule K (Fin n → K)) :
    finrank ℂ (Submodule.span ℂ (j '' (A : Set (Fin n → K)))) ≤ finrank K A := by
  classical
  let b := Module.finBasis K A
  have hle : Submodule.span ℂ (j '' (A : Set (Fin n → K))) ≤ Submodule.span ℂ (Set.range fun k => j (b k : Fin n → K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have e : x = ∑ k, (b.repr ⟨x, hx⟩ k) • (b k : Fin n → K) := by
      have h0 := congrArg (fun v : A => (v : Fin n → K)) (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h0
      exact h0.symm
    rw [e, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine le_trans (Submodule.finrank_mono hle) ?_
  have := finrank_range_le_card (R := ℂ) (fun k => j (b k : Fin n → K))
  simpa [Set.finrank] using this
end Formalism.L2.N.ExtNRows
