-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.tendsto_LIMf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:41.326364+00:00
-- url     : https://prove2.me/submissions/6e3ab0f4-4a6d-464d-b73f-b85e6b02157f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_avg_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_tendsto_lim_of_bdd

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
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (hg : Bdd g) :
    Tendsto (avg e c g) (hyperfilter ℕ : Filter ℕ) (𝓝 (LIMf e c g)) := by
  obtain ⟨B, hB⟩ := hg
  exact tendsto_lim_of_bdd _ B (avg_norm_le e c g B hB)
end Formalism.FourierDecayAlt.P.BoxAverageLimits
