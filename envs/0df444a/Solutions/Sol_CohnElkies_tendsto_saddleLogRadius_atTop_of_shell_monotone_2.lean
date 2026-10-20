-- Prove2me | solution 2 for CohnElkies.tendsto_saddleLogRadius_atTop_of_shell_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:41:00.622983+00:00
-- url     : https://prove2.me/submissions/0e788b66-1db3-4786-b28f-e875ad76214c

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    {d : ℕ} (hd : 0 < d)
    (hmono : MonotoneOn (saddleSourceShellDerivative ε)
      (Ici (1 + ε / 2))) :
    Tendsto (saddleLogRadius ε d) atTop atTop := by
  have hdig : Tendsto saddleDigamma atTop atTop := by
    have h := tendsto_saddleDigamma_sub_log.add_atTop Real.tendsto_log_atTop
    refine h.congr ?_
    intro x; simp
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hd' : (0:ℝ) < (d : ℝ) / 2 / 2 := by positivity
  have harg : Tendsto (fun u : ℝ => ((d : ℝ) / 2) * (1 + u) / 2) atTop atTop := by
    have : (fun u : ℝ => ((d : ℝ) / 2) * (1 + u) / 2) = fun u => (d : ℝ) / 2 / 2 * u + (d : ℝ) / 2 / 2 := by
      funext u; ring
    rw [this]
    exact Filter.tendsto_atTop_add_const_right _ _ (Filter.Tendsto.const_mul_atTop hd' Filter.tendsto_id)
  have hD := ((hdig.comp harg).atTop_div_const (by norm_num : (0:ℝ) < 2))
  set c := saddleSourceShellDerivative ε (1 + ε / 2)
  have hlow : Tendsto (fun u : ℝ => -(Real.log Real.pi) / 2 +
      saddleDigamma (((d : ℝ) / 2) * (1 + u) / 2) / 2 + c) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ _ (Filter.tendsto_atTop_add_const_left _ _ hD)
  refine Filter.tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [Filter.eventually_ge_atTop (1 + ε / 2)] with u hu
  have hm := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  have e : saddleLogRadius ε d u = -(Real.log Real.pi) / 2 +
      saddleDigamma (((d : ℝ) / 2) * (1 + u) / 2) / 2 + saddleSourceShellDerivative ε u := by
    unfold saddleLogRadius saddleSourceShellDerivative; ring
  rw [e]
  linarith

