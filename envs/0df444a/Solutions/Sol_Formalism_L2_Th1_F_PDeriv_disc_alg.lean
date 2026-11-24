-- Prove2me | solution 1 for Formalism.L2.Th1.F.PDeriv.disc_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:25:03.810797+00:00
-- url     : https://prove2.me/submissions/8d8a78ef-9306-4e8e-8c29-989c189a45e9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_PDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PDeriv
namespace Formalism.L2.Th1.F.PDeriv
theorem _root_.solution (g2 g3 e1 e2 e3 : ℂ) (h1 : 4 * e1 ^ 3 - g2 * e1 - g3 = 0)
    (h2 : 4 * e2 ^ 3 - g2 * e2 - g3 = 0) (h3 : 4 * e3 ^ 3 - g2 * e3 - g3 = 0)
    (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3) : g2 ^ 3 - 27 * g3 ^ 2 ≠ 0 := by
  have hA : g2 = 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) := by
    have h0 : (e1 - e2) * (4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) - g2) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) h12
    · linear_combination -h
  have hB : g2 = 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) := by
    have h0 : (e1 - e3) * (4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) - g2) = 0 := by
      linear_combination h1 - h3
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) h13
    · linear_combination -h
  have hS : e1 + e2 + e3 = 0 := by
    have h0 : (e2 - e3) * (e1 + e2 + e3) = 0 := by linear_combination (hB - hA) / 4
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) h23
    · exact h
  have hD : g2 ^ 3 - 27 * g3 ^ 2 = 16 * ((e1 - e2) * (e1 - e3) * (e2 - e3)) ^ 2 := by
    have h3' : e3 = -e1 - e2 := by linear_combination hS
    have hg3 : g3 = 4 * e1 ^ 3 - g2 * e1 := by linear_combination -h1
    rw [hg3, hA, h3']
    ring
  rw [hD]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)) (sub_ne_zero.mpr h23)))
end Formalism.L2.Th1.F.PDeriv
