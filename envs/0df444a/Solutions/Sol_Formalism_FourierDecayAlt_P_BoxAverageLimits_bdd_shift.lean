-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.bdd_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:55.99424+00:00
-- url     : https://prove2.me/submissions/21ccfde3-cb04-41ed-b0a4-335119f1c0ff

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution {g : Λ → ℂ} (hg : Bdd g) (σ : Λ) : Bdd (fun x => g (x + σ)) := by
  obtain ⟨B, hB⟩ := hg; exact ⟨B, fun x => hB _⟩
end Formalism.FourierDecayAlt.P.BoxAverageLimits
