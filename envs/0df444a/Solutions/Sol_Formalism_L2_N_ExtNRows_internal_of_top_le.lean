-- Prove2me | solution 1 for Formalism.L2.N.ExtNRows.internal_of_top_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:35.703078+00:00
-- url     : https://prove2.me/submissions/553602b1-9ac4-4abe-be99-0fdf28d221ce

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → Submodule ℂ W) (ht : (⨆ i, B i) = ⊤)
    (hle : ∑ i, finrank ℂ (B i) ≤ finrank ℂ W) : DirectSum.IsInternal B := by
  have hr : LinearMap.range (DirectSum.coeLinearMap B) = ⊤ := by rw [DirectSum.range_coeLinearMap, ht]
  have hs : Function.Surjective (DirectSum.coeLinearMap B) := LinearMap.range_eq_top.1 hr
  have h1 : finrank ℂ W ≤ finrank ℂ (DirectSum ι fun i => B i) := by
    have := LinearMap.finrank_range_le (DirectSum.coeLinearMap B)
    rwa [hr, finrank_top] at this
  have h2 : finrank ℂ (DirectSum ι fun i => B i) = finrank ℂ W :=
    le_antisymm (by rw [Module.finrank_directSum]; exact hle) h1
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank h2).2 hs, hs⟩
end Formalism.L2.N.ExtNRows
