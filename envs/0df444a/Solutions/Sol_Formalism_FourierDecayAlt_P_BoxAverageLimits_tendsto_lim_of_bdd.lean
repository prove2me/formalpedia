-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.tendsto_lim_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:52.850119+00:00
-- url     : https://prove2.me/submissions/f596c7a4-b282-4b2d-8258-da65bc9ba0b4

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
theorem _root_.solution (u : ℕ → ℂ) (B : ℝ) (hu : ∀ n, ‖u n‖ ≤ B) :
    Tendsto u (hyperfilter ℕ : Filter ℕ) (𝓝 (limUnder (hyperfilter ℕ : Filter ℕ) u)) := by
  have hc : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall 0 B
  obtain ⟨x, -, hx⟩ := hc.ultrafilter_le_nhds ((hyperfilter ℕ).map u) (by
    rw [Ultrafilter.coe_map, le_principal_iff, Filter.mem_map]
    exact Filter.univ_mem' (fun n => by simpa using hu n))
  exact tendsto_nhds_limUnder ⟨x, hx⟩
end Formalism.FourierDecayAlt.P.BoxAverageLimits
