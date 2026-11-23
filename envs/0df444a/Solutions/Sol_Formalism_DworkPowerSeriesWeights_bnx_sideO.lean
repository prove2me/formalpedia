-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_sideO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:38.045827+00:00
-- url     : https://prove2.me/submissions/fb1fa6a4-259b-4495-a059-96138257186f

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_degree_bnxM
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_update_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_oddDerivative_binomial_coeff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bnx_dot_const
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
variable {K : Type u} [NormedField K] {d : ℕ} [NeZero d]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (be : MvPowerSeries (ZMod d) K) (pi r w : ℝ) (h2 : WtGe pi (fun _ => r) w (de2 be))
    (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 ≠ 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 ≠ 0 ∧ t ≠ s ∧ n t ≠ 0) :
    ‖coeff n be‖ * ‖((n s).choose j : K)‖ ≤ pi ^ (w - dot n (fun _ => r)) := by
  have h := h2 (bnxM n (Function.update (⇑n) s j))
  unfold MonoWtGe at h
  rw [oddDerivative_binomial_coeff be n s hs j hj hpos, norm_mul, bnx_dot_const,
    bnx_degree_bnxM n _ (bnx_update_le n s j hj), ← bnx_dot_const] at h
  exact h
end Formalism.DworkPowerSeriesWeights
