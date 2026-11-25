-- Prove2me | solution 1 for Formalism.IncomingBounds.expWeight_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:56.393305+00:00
-- url     : https://prove2.me/submissions/6cd5ffb1-9d5c-418a-b1b3-653a4e3910d5

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Theorems.Thm_Formalism_IncomingBounds_thmPExp_wt_le_add_iff
import Theorems.Thm_Formalism_IncomingBounds_thmPExp_val_coeff_pow
import Theorems.Thm_Formalism_IncomingBounds_padicValFactorialBounds


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
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution (hV : ValNat) : ExpWeight := by
  intro K _ _ v l hl hvl hvp σ w hw h hh hwt m
  have hl2 : (2:ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hpos : (0:ℝ) < (l:ℝ) - 1 := by linarith
  have hc0 : (0:ℝ) < 1 / ((l:ℝ) - 1) := by positivity
  have hh' : ∀ m, ((1 / ((l:ℝ) - 1) - w m : ℝ) : WithTop ℝ) ≤ v (coeff m h) :=
    fun m => (thmPExp_wt_le_add_iff _ _ _).1 (hwt m)
  have hpow := thmPExp_val_coeff_pow v w hw _ h hh'
  rw [show (0 : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) from rfl, thmPExp_wt_le_add_iff, zero_sub]
  change _ ≤ v (∑ k ∈ range (m.degree + 1), coeff m (h ^ k) / (k.factorial : K))
  apply AddValuation.map_le_sum
  intro k _
  have hfk := hV K v l hl hvl hvp k.factorial (Nat.factorial_ne_zero k)
  have hkne : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hdiv : v (coeff m (h ^ k) / (k.factorial : K)) + v (k.factorial : K) =
      v (coeff m (h ^ k)) := by
    rw [← AddValuation.map_mul, div_mul_cancel₀ _ hkne]
  rw [hfk] at hdiv
  have hbound : (padicValNat l k.factorial : ℝ) ≤ (k : ℝ) * (1 / ((l:ℝ) - 1)) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · calc (padicValNat l k.factorial : ℝ) ≤ ((k:ℝ) - 1) / ((l:ℝ) - 1) :=
            (padicValFactorialBounds l hl k hk).2
        _ ≤ (k : ℝ) * (1 / ((l:ℝ) - 1)) := by
            rw [mul_one_div]; gcongr; linarith
  have hlow := hpow k m
  rw [← hdiv, thmPExp_wt_le_add_iff] at hlow
  exact le_trans (WithTop.coe_le_coe.2 (by linarith)) hlow
end Formalism.IncomingBounds
