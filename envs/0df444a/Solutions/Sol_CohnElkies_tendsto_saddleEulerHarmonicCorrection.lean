-- Prove2me | solution 1 for CohnElkies.tendsto_saddleEulerHarmonicCorrection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/76ca1fe6-fb77-4a4a-8356-4c32a002be0e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleDigamma_add_nat

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {m : ℝ} (hm : 0 < m) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) -
          ∑ k ∈ Finset.range (n + 1),
            (m + (k : ℝ))⁻¹)
      atTop (𝓝 (saddleDigamma m)) := by
  have hcast := tendsto_natCast_atTop_atTop
    (R := ℝ)
  have hscale :
      Tendsto
        (fun n : ℕ => m + (n : ℝ) + 1)
        atTop atTop := by
    have h := hcast.atTop_add
      (tendsto_const_nhds (x := m + 1))
    convert! h using 1
    funext n
    ring
  have hdigamma :=
    tendsto_saddleDigamma_sub_log.comp hscale
  have hinv :=
    (tendsto_inv_atTop_nhds_zero_nat
      (𝕜 := ℝ)).const_mul (m + 1)
  have hratio :
      Tendsto
        (fun n : ℕ =>
          (m + (n : ℝ) + 1) / (n : ℝ))
        atTop (𝓝 (1 : ℝ)) := by
    have h :=
      (tendsto_const_nhds (x := (1 : ℝ))).add
        hinv
    have h' :
        Tendsto
          (fun n : ℕ =>
            1 + (m + 1) * (n : ℝ)⁻¹)
          atTop (𝓝 (1 : ℝ)) := by
      simpa using! h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)]
      with n hn
    have hnreal : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn.ne'
    field_simp [hnreal]
    ring
  have hlogratio := hratio.log
    (by norm_num : (1 : ℝ) ≠ 0)
  have hlogdiff :
      Tendsto
        (fun n : ℕ =>
          Real.log (m + (n : ℝ) + 1) -
            Real.log (n : ℝ))
        atTop (𝓝 0) := by
    have h :
        Tendsto
          (fun n : ℕ =>
            Real.log
              ((m + (n : ℝ) + 1) / (n : ℝ)))
          atTop (𝓝 0) := by
      simpa using! hlogratio
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)]
      with n hn
    have hnreal : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn.ne'
    have hmreal : m + (n : ℝ) + 1 ≠ 0 := by
      have : 0 < m + (n : ℝ) + 1 := by positivity
      exact this.ne'
    rw [Real.log_div hmreal hnreal]
  have hzero := (hdigamma.add hlogdiff).neg
  have hlimit := hzero.add_const (saddleDigamma m)
  have hlimit' :
      Tendsto
        (fun n : ℕ =>
          -((saddleDigamma (m + (n : ℝ) + 1) -
              Real.log (m + (n : ℝ) + 1)) +
            (Real.log (m + (n : ℝ) + 1) -
              Real.log (n : ℝ))) +
            saddleDigamma m)
        atTop (𝓝 (saddleDigamma m)) := by
    simpa [Function.comp_apply] using! hlimit
  apply hlimit'.congr'
  filter_upwards [] with n
  have hrec := saddleDigamma_add_nat hm (n + 1)
  push_cast at hrec
  rw [show m + ((n : ℝ) + 1) =
    m + (n : ℝ) + 1 by ring] at hrec
  linarith
end CohnElkies
