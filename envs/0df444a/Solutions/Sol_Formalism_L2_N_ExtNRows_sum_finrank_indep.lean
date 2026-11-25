-- Prove2me | solution 1 for Formalism.L2.N.ExtNRows.sum_finrank_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:39.871848+00:00
-- url     : https://prove2.me/submissions/690f3bec-55a4-4051-ad15-b338b04bc119

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
theorem _root_.solution {ι : Type} [Fintype ι] (B : ι → Submodule ℂ W) (hi : iSupIndep B) :
    ∑ i, finrank ℂ (B i) = finrank ℂ (⨆ i, B i : Submodule ℂ W) := by
  classical
  have hinj : Function.Injective (DirectSum.coeLinearMap B) := hi.dfinsupp_lsum_injective
  rw [← Module.finrank_directSum, ← LinearMap.finrank_range_of_inj hinj, DirectSum.range_coeLinearMap]
end Formalism.L2.N.ExtNRows
