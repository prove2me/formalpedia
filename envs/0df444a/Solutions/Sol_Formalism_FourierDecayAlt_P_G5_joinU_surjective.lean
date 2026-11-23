-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.joinU_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:19.153977+00:00
-- url     : https://prove2.me/submissions/11b70124-1867-4a97-b367-6947d10be2bc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_joinU_idx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution (n : ℕ) : Function.Surjective (joinU : (UT n → ℂ) × (Fin n → ℂ) → UT (n + 1) → ℂ) := by
  intro k
  refine ⟨(fun p => k (idxEquiv n (Sum.inl p)), fun i => k (idxEquiv n (Sum.inr i))), ?_⟩
  funext p
  obtain ⟨s, rfl⟩ := (idxEquiv n).surjective p
  rw [joinU_idx]
  rcases s with p | i <;> rfl
end Formalism.FourierDecayAlt.P.G5
