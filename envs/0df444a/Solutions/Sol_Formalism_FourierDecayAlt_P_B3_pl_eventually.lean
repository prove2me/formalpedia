-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.pl_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:02:26.384468+00:00
-- url     : https://prove2.me/submissions/3df8ab47-c173-4504-a34d-c90c4f7d309f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B3
theorem _root_.solution {a b x : ℝ} (hx : x ∈ Ioo a b) : ∀ᶠ n : ℕ in atTop, pl a b n x = 1 := by
  have hxa : 0 < x - a := by linarith [hx.1]
  have hbx : 0 < b - x := by linarith [hx.2]
  obtain ⟨N, hN⟩ := exists_nat_ge (max (1 / (x - a)) (1 / (b - x)))
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hn' : max (1 / (x - a)) (1 / (b - x)) ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
  apply pl_eq_one
  · have h1 : 1 / (x - a) * (x - a) ≤ (n : ℝ) * (x - a) :=
      mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) hn') hxa.le
    rwa [one_div_mul_cancel hxa.ne'] at h1
  · have h1 : 1 / (b - x) * (b - x) ≤ (n : ℝ) * (b - x) :=
      mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) hn') hbx.le
    rwa [one_div_mul_cancel hbx.ne'] at h1
end Formalism.FourierDecayAlt.P.B3
