-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.LIMf_eq_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:45.975881+00:00
-- url     : https://prove2.me/submissions/c77c1ba4-f31b-4ef6-8f6e-3d3a0476f4fd

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
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (a : ℂ)
    (h : Tendsto (avg e c g) (hyperfilter ℕ : Filter ℕ) (𝓝 a)) : LIMf e c g = a :=
  h.limUnder_eq
end Formalism.FourierDecayAlt.P.BoxAverageLimits
