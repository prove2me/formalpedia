-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.SmOn.of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:27:40.229858+00:00
-- url     : https://prove2.me/submissions/937379ca-7eb1-4ec3-89d6-8f3607f41b33

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace CompanionTheory.D.Upq.Sm
namespace SmOn
theorem _root_.solution {A : Set E} {f : E → V} (hf : ContDiff ℝ ∞ f) : SmOn A f :=
  fun _ _ => ⟨univ, f, isOpen_univ, mem_univ _, hf.contDiffOn, fun _ _ _ => rfl⟩
end SmOn
end CompanionTheory.D.Upq.Sm
