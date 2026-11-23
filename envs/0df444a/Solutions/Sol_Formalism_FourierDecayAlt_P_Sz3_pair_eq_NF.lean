-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.pair_eq_NF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:05.366929+00:00
-- url     : https://prove2.me/submissions/30e73388-3f53-4c0f-a607-8189e5250238

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_pair_reindex
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_shift_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (J : ℕ) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, (de i' - de i) / (4 * ((i' : ℝ) - (i : ℝ))) =
      (1 / 4) * NF J de := by
  rw [pair_reindex, NF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mem_Icc] at hd
  rw [← shift_sum J d hd.2 de, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hd0 : (d : ℝ) ≠ 0 := by
    have : 0 < d := by omega
    positivity
  push_cast
  have : 4 * ((i : ℝ) + d - i) = 4 * d := by ring
  rw [this]
  field_simp
end Formalism.FourierDecayAlt.P.Sz3
