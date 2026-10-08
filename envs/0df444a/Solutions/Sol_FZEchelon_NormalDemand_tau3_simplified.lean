-- Prove2me | solution 1 for FZEchelon.NormalDemand.tau3_simplified
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:16:20.472015+00:00
-- url     : https://prove2.me/submissions/e6a99d05-2965-43a1-9ca2-7f19b80d30bf

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology

open FZEchelon.NormalDemand FZEchelon.NormalDemand.Data in
theorem solution (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    ∀ x : ℝ, D.tau3 x
      = -(x - (((D.L + D.l + 1 : ℕ) : ℝ) / ((D.l + 1 : ℕ) : ℝ)) * D.xstar)
        / (Real.sqrt ((((D.L + D.l + 1 : ℕ) : ℝ) / ((D.l + 1 : ℕ) : ℝ))) * Real.sqrt (D.L : ℝ) * D.σ) := by
  intro x
  have hb : (0:ℝ) < ((D.l + 1 : ℕ) : ℝ) := by positivity
  have hc : (0:ℝ) < ((D.L + D.l + 1 : ℕ) : ℝ) := by positivity
  have hLr : (0:ℝ) < (D.L : ℝ) := by exact_mod_cast hL
  have hsb := Real.sqrt_pos.2 hb
  have hsc := Real.sqrt_pos.2 hc
  have hsL := Real.sqrt_pos.2 hLr
  have hb2 := Real.sq_sqrt hb.le
  have hL2 := Real.sq_sqrt hLr.le
  have hcd : ((D.L + D.l + 1 : ℕ) : ℝ) = (D.L:ℝ) + ((D.l + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [Real.sqrt_div hc.le]
  simp only [Data.tau3, Data.sd, Data.mean]
  have hq : (Real.sqrt (D.L : ℝ) * D.σ / (Real.sqrt ((D.l + 1 : ℕ) : ℝ) * D.σ)) ^ 2
      = (D.L : ℝ) / ((D.l + 1 : ℕ) : ℝ) := by
    rw [div_pow, mul_pow, mul_pow, hb2, hL2]
    field_simp
  rw [hq]
  generalize Real.sqrt ((D.L + D.l + 1 : ℕ) : ℝ) = s at hsc ⊢
  rw [hcd]
  field_simp
  ring
