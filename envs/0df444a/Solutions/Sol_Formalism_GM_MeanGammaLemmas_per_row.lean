-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.per_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:28.580568+00:00
-- url     : https://prove2.me/submissions/4664adcb-f619-41bd-8e55-8b6b5d8f514f

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_vfact_le
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_nlog_le
import Theorems.Thm_P2M_Formalism_GM_MeanGammaLemmas_legendre__b162c2e67de1
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_vchoose_le
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_negLog_beta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Finset
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (a r S o z e cI : ℕ) (κ C : ℝ)
    (heo : e ≤ o) (ho : o ≤ 2 * a) (hS : S ≤ 2 * a) (hz : z ≤ 2 * a) (hr : 1 ≤ r)
    (hκ : 12 * (Real.logb p (8 * a + r) + 1) ≤ κ) (hcI : (cI : ℝ) ≤ C * κ) :
    -Real.logb p ‖(p : ℚ_[p]) ^ (⌈κ⌉₊ + cI) * ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) /
        ((o.factorial * S.factorial : ℕ) : ℚ_[p])‖ + ((S + o - e : ℕ) : ℝ) / ((p : ℝ) - 1) + κ ≤
      (C + 3) * κ := by
  rw [negLog_beta]
  have hp1r : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have L0 : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp1r (by linarith)
  have hκ0 : 0 ≤ κ := by linarith
  have hzl : (Nat.log p (z + e) : ℝ) ≤ Real.logb p (8 * a + r) := by
    have := nlog_le p (z + e) (8 * a + r) (by omega)
    push_cast at this
    exact this
  have hol : (Nat.log p o : ℝ) ≤ Real.logb p (8 * a + r) := by
    have := nlog_le p o (8 * a + r) (by omega)
    push_cast at this
    exact this
  have hSl : (Nat.log p S : ℝ) ≤ Real.logb p (8 * a + r) := by
    have := nlog_le p S (8 * a + r) (by omega)
    push_cast at this
    exact this
  have h1 := vfact_le p e
  have h2 := legendre' p o
  have h3 := legendre' p S
  have h4 := vchoose_le p (z + e) e
  have hceil := Nat.ceil_lt_add_one hκ0
  have hSoe : ((S + o - e : ℕ) : ℝ) = (S : ℝ) + o - e := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hsplit : (e : ℝ) / ((p : ℝ) - 1) + ((S : ℝ) + o - e) / ((p : ℝ) - 1) =
      (S : ℝ) / ((p : ℝ) - 1) + (o : ℝ) / ((p : ℝ) - 1) := by
    rw [← add_div, ← add_div]
    congr 1
    ring
  rw [hSoe]
  push_cast
  linarith
end Formalism.GM.MeanGammaLemmas
