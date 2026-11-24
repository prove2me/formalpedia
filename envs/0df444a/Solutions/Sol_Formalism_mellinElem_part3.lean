-- Prove2me | solution 1 for Formalism.mellinElem_part3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:31.133572+00:00
-- url     : https://prove2.me/submissions/2a38b9ef-4685-49e0-a0ba-35680089840d

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution (a : ℝ) (s : ℂ) (h : a < s.re) :
    ∫ x in Ioi (1:ℝ), ((x ^ a : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - a) := by
  have e : EqOn (fun x : ℝ => ((x ^ a : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => (x : ℂ) ^ ((a : ℂ) - s - 1)) (Ioi 1) := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    simp only
    rw [ofReal_cpow hx0.le, ← cpow_add _ _ (ofReal_ne_zero.mpr hx0.ne')]
    ring_nf
  have hre : ((a : ℂ) - s - 1).re < -1 := by simp; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_Ioi_cpow_of_lt hre one_pos,
    ofReal_one, one_cpow, show (a : ℂ) - s - 1 + 1 = -(s - a) by ring, neg_div_neg_eq]
end Formalism
